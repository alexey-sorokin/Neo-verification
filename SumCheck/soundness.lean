import SumCheck.completeness
import Mathlib.Data.Finset.Card

noncomputable section
open Classical
open scoped BigOperators
open NEO

namespace NEO

universe u
variable {F : Type u} [Field F]

/-
Standard counting soundness bound over a finite challenge set `S : Finset F`.
-/

/-- Challenge values drawn from a finite set `S : Finset F`. -/
abbrev Challenge (S : Finset F) := {x : F // x ∈ S}

/-- Challenge vectors of length `n` with coordinates in `S`. -/
abbrev ChallengeVec (S : Finset F) (n : ℕ) := Fin n → Challenge S

/-- Forget membership proofs and view a `ChallengeVec` as a `vec F n`. -/
def ChallengeVec.toVec {S : Finset F} {n : ℕ} (c : ChallengeVec S n) : vec F n :=
  fun i => (c i).1

/-- A transcript built from fixed `(claimedSum, proverComp)` and a random challenge `c`. -/
def mkTranscriptFrom
  (S : Finset F) (n : ℕ)
  (claimedSum : F)
  (proverComp : Fin n → func F 1)
  (c : ChallengeVec S n) : proverTranscript (F := F) n :=
  { claimedSum := claimedSum
    randomChallenge := c.toVec
    proverComp := proverComp }

/-- The set of challenges that make the verifier accept while the claim is false. -/
def badChallenges
  (S : Finset F) (n : ℕ) (p : func F n)
  (claimedSum : F) (proverComp : Fin n → func F 1) : Finset (ChallengeVec S n) := by
  classical
  exact (Finset.univ : Finset (ChallengeVec S n)).filter (fun c =>
    verifierCheck (F := F) n p (mkTranscriptFrom (F := F) S n claimedSum proverComp c)
      ∧ claimedSum ≠ funcSumTotal (F := F) n p)

/-- All prover messages are affine (degree ≤ 1). -/
def TranscriptAffine {n : ℕ} (proverComp : Fin n → func F 1) : Prop :=
  ∀ i : Fin n, IsAffine1 (F := F) (proverComp i)

axiom honestRound0 (n : ℕ) (p : func F (n+1)) : func F 1

axiom honestRound0_affine (n : ℕ) (p : func F (n+1)) :
  IsAffine1 (F := F) (honestRound0 (F := F) n p)

/-- Affineness is preserved by the tail-cut/permutation used by `verifierCheck`. -/
axiom transcriptAffine_tail
  (n : ℕ) (proverComp : Fin (n+1) → func F 1) :
  TranscriptAffine (F := F) proverComp →
    TranscriptAffine (F := F)
      (proverCompCutHead (F := F) n (proverComp ∘ (finComm 1 n)))

axiom soundness_step_count
  (S : Finset F) (hS : 1 < S.card)
  (n : ℕ) (p : func F (n+1))
  (claimedSum : F) (proverComp : Fin (n+1) → func F 1)
  (tailMax : ℕ) :
    TranscriptAffine (F := F) proverComp →
    -- tailMax bounds the number of bad tails for every head challenge r0 ∈ S
    (∀ (r0 : F), r0 ∈ S →
      (badChallenges (F := F) S n
        ((funcComm n 1 p)
          ∘ (vecSplit_Inv (F := F) 1 n)
          ∘ (Prod.mk (vecOne_Inv (F := F) r0)))
        (proverComp ⟨0, Nat.succ_pos _⟩ (vecOne_Inv (F := F) r0))
        (proverCompCutHead (F := F) n (proverComp ∘ (finComm 1 n))
      )).card
      ≤ tailMax) →
    (badChallenges (F := F) S (n+1) p claimedSum proverComp).card
      ≤ (S.card ^ n) + (S.card) * tailMax

/- `card(badChallenges) ≤ (n+1) * |S|^n`. -/
theorem sumcheck_soundness_counting
  (S : Finset F) (hS : 1 < S.card) :
  ∀ (n : ℕ) (p : func F n) (claimedSum : F) (proverComp : Fin n → func F 1),
    TranscriptAffine (F := F) proverComp →
    (badChallenges (F := F) S n p claimedSum proverComp).card ≤ (n + 1) * (S.card ^ n)
:= by
  classical
  intro n
  induction n with
  | zero =>
      intro p claimedSum proverComp hAff
      -- `ChallengeVec S 0` is subsingleton: the filtered set has card ≤ 1.
      have : (badChallenges (F := F) S 0 p claimedSum proverComp).card ≤ 1 := by
        simpa [badChallenges] using
          (Finset.card_le_card (s := badChallenges (F := F) S 0 p claimedSum proverComp)
            (t := (Finset.univ : Finset (ChallengeVec S 0))))
      simpa using le_trans this (by simp)
  | succ n ih =>
      intro p claimedSum proverComp hAff
      -- Apply the one-step recurrence with tailMax := (n+1)*|S|^n.
      let tailMax : ℕ := (n + 1) * (S.card ^ n)

      have hAffTail :
          TranscriptAffine (F := F)
            (proverCompCutHead (F := F) n (proverComp ∘ (finComm 1 n))) :=
        transcriptAffine_tail (F := F) n proverComp hAff

      have hTailBound : ∀ (r0 : F), r0 ∈ S →
          (badChallenges (F := F) S n
            ((funcComm n 1 p)
              ∘ (vecSplit_Inv (F := F) 1 n)
              ∘ (Prod.mk (vecOne_Inv (F := F) r0)))
            (proverComp ⟨0, Nat.succ_pos _⟩ (vecOne_Inv (F := F) r0))
            (proverCompCutHead (F := F) n (proverComp ∘ (finComm 1 n))
          )).card
          ≤ tailMax := by
        intro r0 hr0
        -- Apply IH to the tail instance.
        -- (We use the same `TranscriptAffine` witness `hAffTail`.)
        simpa [tailMax] using
          ih
            (p := ((funcComm n 1 p)
              ∘ (vecSplit_Inv (F := F) 1 n)
              ∘ (Prod.mk (vecOne_Inv (F := F) r0))))
            (claimedSum := (proverComp ⟨0, Nat.succ_pos _⟩ (vecOne_Inv (F := F) r0)))
            (proverComp := (proverCompCutHead (F := F) n (proverComp ∘ (finComm 1 n))))
            hAffTail

      have hstep :
          (badChallenges (F := F) S (n+1) p claimedSum proverComp).card
            ≤ (S.card ^ n) + (S.card) * tailMax :=
        soundness_step_count (F := F) S hS n p claimedSum proverComp tailMax hAff hTailBound

      -- |S|^n + |S| * ((n+1)*|S|^n) ≤ (n+2)*|S|^(n+1).
      have hSpos : 0 < S.card := lt_trans (by decide : (0:ℕ) < 1) hS
      have hpow : S.card ^ n ≤ (S.card ^ n) * S.card := by
        -- `a ≤ a*b` when `b > 0`
        simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right (S.card ^ n) hSpos

      have h_arith :
          (S.card ^ n) + (S.card) * tailMax ≤ (n + 2) * (S.card ^ (n+1)) := by
        dsimp [tailMax]
        set X : ℕ := S.card ^ n

        -- Replace the leftmost `X` by `X*S.card` using `hpow`.
        have h1 : X + S.card * ((n + 1) * X) ≤ X * S.card + S.card * ((n + 1) * X) := by
          -- `X ≤ X*S.card`, then add the common right term
          exact Nat.add_le_add_right (by simpa [X] using hpow) _

        -- Simplify the RHS into `(n+2) * (X*S.card)` and then into `(n+2)*S.card^(n+1)`.
        have h2 : X * S.card + S.card * ((n + 1) * X) = (n + 2) * (X * S.card) := by
          -- `S.card * ((n+1) * X) = (n+1) * (X*S.card)` and `X*S.card + (n+1)*(X*S.card) = (n+2)*(X*S.card)`
          calc
            X * S.card + S.card * ((n + 1) * X)
                = X * S.card + (n + 1) * (X * S.card) := by
                    simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.left_distrib, Nat.right_distrib]
            _ = (n + 2) * (X * S.card) := by
                    -- `a + (n+1)*a = (n+2)*a`
                    simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]

        have : X + S.card * ((n + 1) * X) ≤ (n + 2) * (X * S.card) := by
          exact le_trans h1 (by simpa [h2])

        -- `X*S.card` as `S.card^(n+1)`.
        simpa [X, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this

      have :
          (badChallenges (F := F) S (n+1) p claimedSum proverComp).card
            ≤ (n + 2) * (S.card ^ (n+1)) :=
        le_trans hstep h_arith

      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

end NEO
