/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration

/-!
# Completed tensor coalgebras

The tensor-length completion of tensor words is the product `∏ n, M^{⊗n}`. Its coproduct
has values in the completed tensor product `∏ p q, M^{⊗p} ⊗ M^{⊗q}`: the `(p,q)` coordinate
splits the length-`p+q` component. We prove coassociativity and both counit identities in
coordinates, including the empty blocks. This is a completed coalgebra, not an ordinary
`Coalgebra` with coproduct in the algebraic tensor square.

Finite tensor words embed by `DFinsupp.coeFnLinearMap R`. Their coproduct agrees with the
completed one after projecting to each bidegree. The length filtration is separated, and
compatible finite truncations determine a unique completed word, so the length filtration is
complete and separated (`isCompleteFiltration_filtration`). Thus the product permits
infinite length support whereas `TensorWords` is the direct-sum coalgebra.

The length-completion convention follows J.-L. Loday and B. Vallette, *Algebraic Operads*,
Chapters 9--10. All tensor-power identifications reuse Mathlib's `TensorPower.mulEquiv`.
-/

public section

open scoped TensorProduct DirectSum

namespace TauCeti

universe u v

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Tensor words completed with respect to tensor length, including the empty word. -/
abbrev CompletedTensorWords := ∀ n : ℕ, TensorPower R n M

namespace CompletedTensorWords

/-- Deconcatenation into the completed tensor square, indexed by the two output lengths. -/
noncomputable def deconcatenation : CompletedTensorWords R M →ₗ[R]
    ∀ p q : ℕ, TensorPower R p M ⊗[R] TensorPower R q M :=
  LinearMap.pi fun p ↦ LinearMap.pi fun q ↦
    (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap ∘ₗ
      LinearMap.proj (p + q)

/-- Each coordinate of the completed coproduct is one cut of one length component. -/
@[simp]
theorem deconcatenation_apply (x : CompletedTensorWords R M) (p q : ℕ) :
    deconcatenation R M x p q =
      (TensorPower.mulEquiv (R := R) (M := M)).symm (x (p + q)) :=
  (rfl)

/-- The completed coproduct is coassociative, with equality tested at each triple of lengths. -/
theorem deconcatenation_coassoc (x : CompletedTensorWords R M) (p q r : ℕ) :
    (TensorProduct.assoc R _ _ _)
      (TensorProduct.map (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap
        LinearMap.id (deconcatenation R M x (p + q) r)) =
      TensorProduct.map LinearMap.id
        (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap
        (deconcatenation R M x p (q + r)) := by
  have hcast {i j : ℕ} (h : i = j) : TensorPower.cast R M h (x i) = x j := by
    subst j
    simp [TensorPower.cast_refl]
  simpa only [deconcatenation_apply, hcast] using
    TensorPower.mulEquiv_symm_assoc R M p q r (x (p + q + r))

/-- The counit reads the scalar coefficient of the empty word. -/
noncomputable def counit : CompletedTensorWords R M →ₗ[R] R :=
  (TensorPower.algebraMap₀ (R := R) (M := M)).symm.toLinearMap ∘ₗ LinearMap.proj 0

/-- Evaluation of the counit is evaluation of the length-zero component. -/
@[simp]
theorem counit_apply (x : CompletedTensorWords R M) :
    counit R M x = (TensorPower.algebraMap₀ (R := R) (M := M)).symm (x 0) :=
  (rfl)

/-- Applying the counit to the first output of the coproduct recovers each component. -/
@[simp↓]
theorem counit_left (x : CompletedTensorWords R M) (n : ℕ) :
    TensorProduct.lid R (TensorPower R n M)
      (TensorProduct.map (TensorPower.algebraMap₀ (R := R) (M := M)).symm.toLinearMap
        LinearMap.id (deconcatenation R M x 0 n)) = x n := by
  rw [TensorPower.lid_map_algebraMap₀_symm, deconcatenation_apply, LinearEquiv.apply_symm_apply]
  have hcast {i j : ℕ} (h : i = j) : TensorPower.cast R M h (x i) = x j := by
    subst j
    simp [TensorPower.cast_refl]
  exact hcast (Nat.zero_add n)

/-- Applying the counit to the second output of the coproduct recovers each component. -/
@[simp↓]
theorem counit_right (x : CompletedTensorWords R M) (n : ℕ) :
    TensorProduct.rid R (TensorPower R n M)
      (TensorProduct.map LinearMap.id
        (TensorPower.algebraMap₀ (R := R) (M := M)).symm.toLinearMap
        (deconcatenation R M x n 0)) = x n := by
  rw [TensorPower.rid_map_algebraMap₀_symm, deconcatenation_apply, LinearEquiv.apply_symm_apply]
  simp [TensorPower.cast_refl]

/-- On finite tensor words the completed coproduct is the ordinary coproduct, projected to
its output bidegree. Thus the canonical direct-sum inclusion respects deconcatenation. -/
@[simp↓]
theorem deconcatenation_coe (x : TensorWords R M) (p q : ℕ) :
    deconcatenation R M (DFinsupp.coeFnLinearMap R x) p q =
      TensorProduct.map (TensorWords.component R M p) (TensorWords.component R M q)
        (TensorWords.deconcatenation R M x) := by
  simpa only [deconcatenation_apply, DFinsupp.coeFnLinearMap_apply,
    TensorWords.component_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe] using
    (LinearMap.congr_fun (TensorWords.map_component_comp_deconcatenation R M p q) x).symm

/-- The inclusion of finite tensor words preserves the counit. -/
@[simp↓]
theorem counit_coe (x : TensorWords R M) :
    counit R M (DFinsupp.coeFnLinearMap R x) = TensorWords.counit R M x := by
  rw [counit_apply, TensorWords.counit_apply, TensorWords.component_apply]
  rfl

/-- Discard all components of length at least `n`, producing an ordinary finite tensor word. -/
noncomputable def truncate (n : ℕ) : CompletedTensorWords R M →ₗ[R] TensorWords R M :=
  DFinsupp.lmk (Finset.range n) ∘ₗ LinearMap.pi fun i ↦ LinearMap.proj i.val

/-- Truncation retains exactly the coordinates below its cutoff. -/
@[simp]
theorem truncate_apply (n : ℕ) (x : CompletedTensorWords R M) (k : ℕ) :
    truncate R M n x k = if k < n then x k else 0 := by
  simp [truncate, DFinsupp.lmk, DFinsupp.mk_apply]

/-- Truncating twice retains the components below the smaller cutoff. -/
@[simp]
theorem truncate_truncate (n m : ℕ) (x : CompletedTensorWords R M) :
    truncate R M n (truncate R M m x) = truncate R M (min n m) x := by
  ext k
  simp only [truncate_apply, lt_min_iff]
  split_ifs <;> simp_all

/-- The descending length filtration consists of words whose components below `n` vanish. -/
def filtration (n : ℕ) : Submodule R (CompletedTensorWords R M) :=
  ⨅ k : Fin n, LinearMap.ker (LinearMap.proj k.val)

/-- Membership in the length filtration is coordinatewise vanishing below the cutoff. -/
@[simp]
theorem mem_filtration (x : CompletedTensorWords R M) (n : ℕ) :
    x ∈ filtration R M n ↔ ∀ k < n, x k = 0 := by
  simp [filtration, LinearMap.mem_ker, Fin.forall_iff]

/-- The length filtration is the kernel of finite truncation. -/
theorem filtration_eq_ker_truncate (n : ℕ) :
    filtration R M n = LinearMap.ker (truncate R M n) := by
  ext x
  rw [mem_filtration, LinearMap.mem_ker]
  constructor
  · intro hx
    ext k
    by_cases hk : k < n <;> simp [truncate_apply, hk, hx]
  · intro hx k hk
    have h := congrArg (fun w : TensorWords R M ↦ w k) hx
    simpa only [truncate_apply, ite_eq_left hk, DFinsupp.zero_apply] using h

/-- The length filtration is decreasing. -/
theorem filtration_antitone : Antitone (filtration R M) := by
  intro n m h x hx
  rw [mem_filtration] at hx ⊢
  exact fun k hk ↦ hx k (lt_of_lt_of_le hk h)

/-- The intersection of the length filtration is zero. -/
@[simp]
theorem iInf_filtration_eq_bot : ⨅ n, filtration R M n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hx' : ∀ n, x ∈ filtration R M n := by simpa only [Submodule.mem_iInf] using hx
  ext k
  exact (mem_filtration R M x (k + 1)).mp (hx' (k + 1)) k
    (Nat.lt_succ_self k)

/-- A word in filtration degree `n` has no coproduct coordinates of total length below `n`.
This expresses continuity of deconcatenation for the total-length filtration. -/
theorem deconcatenation_eq_zero_of_mem_filtration {x : CompletedTensorWords R M} {n p q : ℕ}
    (hx : x ∈ filtration R M n) (hpq : p + q < n) :
    deconcatenation R M x p q = 0 := by
  simp [deconcatenation_apply, (mem_filtration R M x n).mp hx (p + q) hpq]

/-- Completeness for tensor length: every compatible family of finite truncations comes from
exactly one completed word. The compatibility equation also requires each finite word to be
supported below its stated cutoff (take `n = m`). -/
theorem existsUnique_of_compatible_truncations (x : ℕ → TensorWords R M)
    (hx : ∀ n m, n ≤ m → truncate R M n (x m) = x n) :
    ∃! y : CompletedTensorWords R M, ∀ n, truncate R M n y = x n := by
  let y : CompletedTensorWords R M := fun k ↦ x (k + 1) k
  have hy : ∀ n, truncate R M n y = x n := by
    intro n
    ext k
    rw [truncate_apply]
    by_cases hk : k < n
    · rw [ite_eq_left hk]
      have h := congrArg (fun w : TensorWords R M ↦ w k) (hx (k + 1) n (by omega))
      simpa only [truncate_apply, Nat.lt_succ_self, ite_true] using h.symm
    · rw [ite_eq_right hk]
      have h := congrArg (fun w : TensorWords R M ↦ w k) (hx n n le_rfl)
      simpa only [truncate_apply, ite_eq_right hk] using h
  refine ⟨y, hy, fun z hz ↦ ?_⟩
  funext k
  have h := congrArg (fun w : TensorWords R M ↦ w k) (hz (k + 1))
  simpa only [truncate_apply, Nat.lt_succ_self, ite_true] using h

end CompletedTensorWords
end TauCeti

namespace TauCeti.CompletedTensorWords

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The tensor-length filtration of completed tensor words is complete and separated. -/
theorem isCompleteFiltration_filtration : IsCompleteFiltration (filtration R M) :=
  isCompleteFiltration_pi id _ fun n x ↦ mem_filtration R M x n

end TauCeti.CompletedTensorWords
