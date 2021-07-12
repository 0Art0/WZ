import binomial
import WZtheorem

open int
open binomial

/-
Proof of ∑ₖ (binomial n k) / (2^n) = 1

The `sorry`s indicate places where ideally the theorem prover should be able to carry the proof to its completion.
-/


def extendedbinomial : ℤ → ℤ → ℚ
  | (of_nat n) (of_nat k) := binomial n k
  | -[1+n] _ := 0
  | _ -[1+k] := 0

def F : ℤ → ℤ → ℚ := λ n k, (extendedbinomial n k) / (2 ^ n)

def G : ℤ → ℤ → ℚ := λ n k, - (extendedbinomial n (k-1)) / (2 ^ (n+1))

theorem WZ_FG : WZ_pair F G :=
begin
  unfold WZ_pair,
  intros n k,
  rw F at *,
  rw G at *,
  simp,
  ring_nf,
  cases n,
  sorry,
  sorry,
end

theorem Gvanishes : ∀ n, vanishes (G n) :=
begin
  intro n,
  unfold vanishes,
  intro ε, intro hεpos,
  existsi (int.to_nat (n+1)),
  intro k,
  intro hkrange,
  sorry,
end

theorem basecase : summation.equals_indefinite_sum (F 0) 1 :=
begin
  unfold summation.equals_indefinite_sum,
  intro ε, intro hε,
  use 1,
  intro m, intro hmgt1,
  split,
  {
    rw F,
    induction m with d hd,
    {
      rw summation.summation,
      simp,
      linarith,
    },
    {
      rw summation.summation,
      simp,
      simp at hd,
      sorry,
    }
  },
  {
    induction m with d hd,
    linarith,
    rw summation.summation,
    rw F,
    sorry,
  }
end

-- the final theorem
theorem binomial_id : ∀ (n : ℤ), summation.equals_indefinite_sum (F n) 1 := WZ F G WZ_FG Gvanishes 1 basecase
