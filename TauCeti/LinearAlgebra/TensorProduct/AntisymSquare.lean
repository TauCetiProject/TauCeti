/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# The antisymmetric tensor cokernel

For a commutative ring `R` and an `R`-module `M`, `TauCeti.antisymSquare R M` is the cokernel of
`1 + τ` on the tensor square `M ⊗[R] M`, where `τ` is the flip `a ⊗ b ↦ b ⊗ a`. Writing `a ∧ b`
for the class of `a ⊗ b` (the bilinear map `TauCeti.antisymSquare.mk`), it is the universal
target of a bilinear map with `a ∧ b + b ∧ a = 0`. Unlike the exterior square `⋀[R]^2 M`, the
diagonal classes `a ∧ a` need not vanish; they only satisfy `2 • (a ∧ a) = 0`.

This is the target of the boundary map `[x] ↦ x ∧ (1 - x)` of the Bloch group, taken with
`R = ℤ` and `M` the additive group of units of a ring: there the diagonal `2`-torsion is part of
the answer, and passing to the exterior square loses it. The cokernel of `1 + τ` is a different
object from `TauCeti.antisymmetricTensors`, the kernel of `1 + τ` inside the tensor square.

For an abelian group `A` the comparison with the exterior square is exact:
`0 → A/2A → antisymSquare ℤ A → ⋀[ℤ]^2 A → 0`, the first map being `a ↦ a ∧ a`
(`TauCeti.antisymSquare_diagonal_exact`). In particular `1 ∧ 1 ≠ 0` in `antisymSquare ℤ ℤ`, while
`⋀[ℤ]^2 ℤ = 0`.

## Main definitions

* `TauCeti.antisymSquare R M`: the quotient of `M ⊗[R] M` by the range of `id + comm`.
* `TauCeti.antisymSquare.mk`: the bilinear map `(a, b) ↦ a ∧ b`.
* `TauCeti.antisymSquare.diag`: the additive map `a ↦ a ∧ a`.
* `TauCeti.antisymSquare.lift`: the linear map induced by a bilinear map `f` with
  `f a b + f b a = 0`.
* `TauCeti.antisymSquare.map`: the linear map induced by a linear map `M → N`.
* `TauCeti.antisymSquare.toExterior`: the surjection onto `⋀[R]^2 M`, `a ∧ b ↦ ιMulti ![a, b]`.

## Main results

* `TauCeti.antisymSquare.range_id_add_comm`: the relations are spanned by the `a ⊗ b + b ⊗ a`.
* `TauCeti.antisymSquare.ker_toExterior`: the kernel of `toExterior` is spanned by the diagonal
  classes `a ∧ a`.
* `TauCeti.antisymSquare.mk_self_eq_zero_iff`: over `ℤ`, `a ∧ a = 0` exactly when `a ∈ 2A`.
* `TauCeti.antisymSquare.exact_diag_toExterior`: over `ℤ`, the image of `diag` is the kernel of
  `toExterior`.
* `TauCeti.antisymSquare_diagonal_exact`: the exact sequence `0 → A/2A → antisymSquare ℤ A →
  ⋀[ℤ]^2 A → 0`, stated through its maps.

## Implementation notes

`TauCeti.antisymSquare` is an `abbrev` for the quotient module, so its `R`-module structure and
`Submodule.Quotient.mk` apply directly; `TauCeti.antisymSquare.quotientMk_tmul` rewrites the class
of `a ⊗ b` to the wedge `mk R M a b`, the normal form of the rest of the file.

## References

* C. Weibel, *The K-book: an introduction to algebraic K-theory*, Chapter VI, §5, opening
  paragraphs, where this group is the twisted exterior square of `A`.
-/

@[expose] public section

open scoped TensorProduct

namespace TauCeti

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The antisymmetric tensor cokernel: the tensor square `M ⊗[R] M` modulo the range of `1 + τ`,
where `τ` is the flip. The class of `a ⊗ b` is written `a ∧ b` (`TauCeti.antisymSquare.mk`); the
diagonal classes `a ∧ a` are `2`-torsion but need not vanish. -/
abbrev antisymSquare :=
  (M ⊗[R] M) ⧸ LinearMap.range
    ((LinearMap.id : (M ⊗[R] M) →ₗ[R] (M ⊗[R] M)) + (TensorProduct.comm R M M).toLinearMap)

end TauCeti

end

public section

open scoped TensorProduct

namespace TauCeti.antisymSquare

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-! ### The wedge and its relations -/

/-- The relations of `antisymSquare R M` are spanned by the symmetrized tensors
`a ⊗ b + b ⊗ a`. -/
theorem range_id_add_comm :
    LinearMap.range
        ((LinearMap.id : (M ⊗[R] M) →ₗ[R] (M ⊗[R] M)) + (TensorProduct.comm R M M).toLinearMap) =
      Submodule.span R {t | ∃ a b : M, t = a ⊗ₜ[R] b + b ⊗ₜ[R] a} := by
  rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top, Submodule.map_span]
  congr 1
  ext t
  simp [eq_comm]

/-- The wedge `(a, b) ↦ a ∧ b`, the class of `a ⊗ b` in `antisymSquare R M`. -/
noncomputable def mk : M →ₗ[R] M →ₗ[R] antisymSquare R M :=
  (TensorProduct.mk R M M).compr₂ (Submodule.mkQ _)

variable {R M}

/-- The wedge `a ∧ b` is the class of `a ⊗ b`. -/
@[simp]
theorem quotientMk_tmul (a b : M) :
    (Submodule.Quotient.mk (a ⊗ₜ[R] b) : antisymSquare R M) = mk R M a b :=
  (rfl)

/-- The wedge is antisymmetric: `a ∧ b + b ∧ a = 0`. -/
@[simp]
theorem mk_add_mk_swap (a b : M) : mk R M a b + mk R M b a = 0 := by
  rw [← quotientMk_tmul, ← quotientMk_tmul, ← Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_eq_zero]
  exact ⟨a ⊗ₜ b, by simp⟩

/-- The wedge changes sign when its arguments are swapped: `b ∧ a = -(a ∧ b)`. -/
theorem mk_swap (a b : M) : mk R M b a = -mk R M a b :=
  eq_neg_of_add_eq_zero_left (mk_add_mk_swap b a)

/-- The diagonal classes are `2`-torsion: `2 • (a ∧ a) = 0`. -/
@[simp]
theorem two_nsmul_mk_self (a : M) : 2 • mk R M a a = 0 := by
  rw [two_nsmul, mk_add_mk_swap]

/-- The diagonal is additive: `(a + b) ∧ (a + b) = a ∧ a + b ∧ b`. -/
theorem mk_add_self (a b : M) :
    mk R M (a + b) (a + b) = mk R M a a + mk R M b b := by
  simp only [map_add, LinearMap.add_apply, mk_swap b a]
  abel

/-- The wedges `a ∧ b` span `antisymSquare R M`. -/
theorem span_mk : Submodule.span R {z : antisymSquare R M | ∃ a b, mk R M a b = z} = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ z
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact Submodule.subset_span ⟨a, b, rfl⟩
  | add t t' ht ht' => simpa using Submodule.add_mem _ ht ht'

/-- Two linear maps out of `antisymSquare R M` that agree on every wedge `a ∧ b` are equal.

The priority is raised so that `ext` uses this lemma before the extensionality lemmas of the
underlying quotient and tensor product, which would state the goal through `mkQ` and `curry`. -/
@[ext high]
theorem ext {N : Type*} [AddCommGroup N] [Module R N] {f g : antisymSquare R M →ₗ[R] N}
    (h : ∀ a b, f (mk R M a b) = g (mk R M a b)) : f = g :=
  Submodule.linearMap_qext _ <| TensorProduct.ext' fun a b ↦ by
    simpa only [LinearMap.comp_apply, Submodule.mkQ_apply, quotientMk_tmul] using h a b

/-! ### The diagonal -/

variable (R M) in
/-- The diagonal `a ↦ a ∧ a`, an additive map `M → antisymSquare R M`. It need not be
`R`-linear: `(r • a) ∧ (r • a) = r ^ 2 • (a ∧ a)`. Over `R = ℤ`, being additive, it is
`ℤ`-linear. -/
noncomputable def diag : M →+ antisymSquare R M :=
  AddMonoidHom.mk' (fun a ↦ mk R M a a) mk_add_self

/-- The diagonal sends `a` to `a ∧ a`. -/
@[simp]
theorem diag_apply (a : M) : diag R M a = mk R M a a :=
  (rfl)

/-- The diagonal is quadratic in the scalars: `(r • a) ∧ (r • a) = r ^ 2 • (a ∧ a)`. -/
theorem diag_smul (r : R) (a : M) : diag R M (r • a) = r ^ 2 • diag R M a := by
  simp [pow_two, mul_smul]

/-- The diagonal vanishes on `2M`: `(2 • a) ∧ (2 • a) = 0`. -/
theorem diag_two_nsmul (a : M) : diag R M (2 • a) = 0 := by
  rw [map_nsmul, diag_apply, two_nsmul_mk_self]

/-! ### The universal property -/

section Lift

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- A bilinear map `f` with `f a b + f b a = 0` factors through `antisymSquare R M`. -/
noncomputable def lift (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ a b, f a b + f b a = 0) :
    antisymSquare R M →ₗ[R] N :=
  Submodule.liftQ _ (TensorProduct.lift f) <| by
    rw [range_id_add_comm, Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    simp [hf]

/-- The lift sends `a ∧ b` to `f a b`. -/
@[simp]
theorem lift_mk (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ a b, f a b + f b a = 0) (a b : M) :
    lift f hf (mk R M a b) = f a b := by
  rw [← quotientMk_tmul, lift, Submodule.liftQ_apply, TensorProduct.lift.tmul]

/-- The factorization of `f` through the wedge is `f` itself. -/
@[simp]
theorem mk_compr₂_lift (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ a b, f a b + f b a = 0) :
    (mk R M).compr₂ (lift f hf) = f := by
  ext a b
  simp

/-- A linear map out of `antisymSquare R M` is the lift of its composite with the wedge. -/
@[simp]
theorem lift_mk_compr₂ (g : antisymSquare R M →ₗ[R] N) :
    lift ((mk R M).compr₂ g) (fun a b ↦ by simp [← map_add]) = g := by
  ext a b
  simp

end Lift

/-! ### Functoriality -/

section Map

variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A linear map `g : M → N` induces `antisymSquare R M → antisymSquare R N`,
`a ∧ b ↦ g a ∧ g b`. -/
noncomputable def map (g : M →ₗ[R] N) : antisymSquare R M →ₗ[R] antisymSquare R N :=
  lift ((mk R N).compl₁₂ g g) fun a b ↦ by simp

/-- The induced map sends `a ∧ b` to `g a ∧ g b`. -/
@[simp]
theorem map_mk (g : M →ₗ[R] N) (a b : M) : map g (mk R M a b) = mk R N (g a) (g b) := by
  simp [map]

/-- The identity induces the identity. -/
@[simp]
theorem map_id : map (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext a b
  simp

/-- The induced maps compose. -/
theorem map_comp (g : N →ₗ[R] P) (h : M →ₗ[R] N) : map (g ∘ₗ h) = map g ∘ₗ map h := by
  ext a b
  simp

end Map

/-! ### Comparison with the exterior square -/

section Exterior

open _root_.exteriorPower

variable (R M) in
/-- The canonical surjection `antisymSquare R M → ⋀[R]^2 M`, `a ∧ b ↦ ιMulti R 2 ![a, b]`. It
kills the diagonal classes `a ∧ a`. -/
noncomputable def toExterior : antisymSquare R M →ₗ[R] ⋀[R]^2 M :=
  lift (ιMulti R 2).toMultilinearMap.toBilinMap fun a b ↦ by
    simp only [MultilinearMap.toBilinMap_apply, AlternatingMap.coe_multilinearMap]
    rw [ιMulti_two_swap a b, add_neg_cancel]

/-- The comparison with the exterior square sends `a ∧ b` to `ιMulti R 2 ![a, b]`. -/
@[simp]
theorem toExterior_mk (a b : M) : toExterior R M (mk R M a b) = ιMulti R 2 ![a, b] := by
  simp [toExterior]

/-- The comparison with the exterior square kills the diagonal classes. -/
theorem toExterior_mk_self (a : M) : toExterior R M (mk R M a a) = 0 := by
  simp

/-- The comparison with the exterior square is surjective. -/
theorem toExterior_surjective : Function.Surjective (toExterior R M) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← ιMulti_span, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  refine ⟨mk R M (v 0) (v 1), ?_⟩
  rw [toExterior_mk]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The comparison with the exterior square is natural in `M`. -/
theorem toExterior_comp_map {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    toExterior R N ∘ₗ map g = exteriorPower.map 2 g ∘ₗ toExterior R M := by
  ext a b
  simp only [LinearMap.comp_apply, map_mk, toExterior_mk, exteriorPower.map_apply_ιMulti_two]

/-- The kernel of `toExterior` is the submodule spanned by the diagonal classes `a ∧ a`. -/
theorem ker_toExterior :
    LinearMap.ker (toExterior R M) = Submodule.span R (Set.range (diag R M)) := by
  set D := Submodule.span R (Set.range (diag R M))
  refine le_antisymm ?_ ?_
  · -- The wedge modulo `D` is alternating, so it descends to `⋀[R]^2 M` and inverts
    -- `toExterior` modulo `D`.
    have hω : ((mk R M).compr₂ D.mkQ).IsAlt := fun a ↦ by
      simpa using Submodule.subset_span (s := Set.range (diag R M)) ⟨a, rfl⟩
    set φ := alternatingMapLinearEquiv hω.toAlternatingMap
    have hφ : φ ∘ₗ toExterior R M = D.mkQ := by
      ext a b
      simp [φ, alternatingMapLinearEquiv_apply_ιMulti]
    intro z hz
    rw [← Submodule.Quotient.mk_eq_zero, ← D.mkQ_apply, ← hφ, LinearMap.comp_apply,
      LinearMap.mem_ker.mp hz, map_zero]
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact toExterior_mk_self a

end Exterior

/-! ### The diagonal over `ℤ` -/

section Int

variable {A : Type*} [AddCommGroup A]

/-- Over `ℤ`, the diagonal class `a ∧ a` vanishes exactly when `a` is divisible by two. -/
theorem mk_self_eq_zero_iff (a : A) : mk ℤ A a a = 0 ↔ ∃ c, a = 2 • c := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- If `a ∉ 2A`, an additive map `ψ : A → ℤ/2` with `ψ a ≠ 0` exists, since `A/2A` is a
    -- vector space over `ℤ/2`; the pairing `a ∧ b ↦ ψ a * ψ b` then detects `a ∧ a`.
    let H := (nsmulAddMonoidHom 2 : A →+ A).range
    by_contra ha
    let _ : Module (ZMod 2) (A ⧸ H) := QuotientAddGroup.zmodModule fun x ↦ ⟨x, rfl⟩
    have hne : (QuotientAddGroup.mk a : A ⧸ H) ≠ 0 := by
      rw [ne_eq, QuotientAddGroup.eq_zero_iff]
      rintro ⟨c, rfl⟩
      exact ha ⟨c, rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (A ⧸ H), φ (QuotientAddGroup.mk a) ≠ 0 := by
      by_contra! hφ
      exact hne ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp hφ)
    let ψ : A →ₗ[ℤ] ZMod 2 :=
      (φ.toAddMonoidHom.comp (QuotientAddGroup.mk' H)).toIntLinearMap
    let f : A →ₗ[ℤ] A →ₗ[ℤ] ZMod 2 := (LinearMap.mul ℤ (ZMod 2)).compl₁₂ ψ ψ
    have hf : ∀ x y, f x y + f y x = 0 := fun x y ↦ by
      simp only [f, LinearMap.compl₁₂_apply, LinearMap.mul_apply', mul_comm (ψ y)]
      exact CharTwo.add_self_eq_zero _
    have := congr(lift f hf $h)
    simp only [lift_mk, map_zero, f, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at this
    exact mul_self_ne_zero.mpr hφ this
  · rintro ⟨c, rfl⟩
    simp

/-- Over `ℤ`, two diagonal classes agree exactly when their entries agree modulo `2A`. -/
theorem mk_self_eq_mk_self_iff (a b : A) :
    mk ℤ A a a = mk ℤ A b b ↔ ∃ c, a - b = 2 • c := by
  rw [← mk_self_eq_zero_iff, ← diag_apply, ← diag_apply, ← diag_apply, map_sub, sub_eq_zero]

/-- Over `ℤ`, the subgroup spanned by the diagonal classes consists of the diagonal classes. -/
theorem mem_span_range_diag_iff (z : antisymSquare ℤ A) :
    z ∈ Submodule.span ℤ (Set.range (diag ℤ A)) ↔ ∃ a, mk ℤ A a a = z := by
  rw [← (diag ℤ A).coe_range, ← Submodule.mem_toAddSubgroup, Submodule.span_int_eq,
    AddMonoidHom.mem_range]
  simp only [diag_apply]

/-- Over `ℤ`, the diagonal classes are exactly the kernel of the comparison with the exterior
square: `A → antisymSquare ℤ A → ⋀[ℤ]^2 A` is exact. -/
theorem exact_diag_toExterior : Function.Exact (diag ℤ A) (toExterior ℤ A) := fun z ↦ by
  rw [← LinearMap.mem_ker, ker_toExterior, mem_span_range_diag_iff]
  simp only [Set.mem_range, diag_apply]

/-- In `antisymSquare ℤ ℤ` the class `1 ∧ 1` is nonzero, although its image in the exterior
square `⋀[ℤ]^2 ℤ` vanishes. -/
theorem mk_one_one_ne_zero : mk ℤ ℤ 1 1 ≠ 0 := by
  rw [ne_eq, mk_self_eq_zero_iff]
  rintro ⟨c, hc⟩
  rw [two_nsmul] at hc
  omega

end Int

end TauCeti.antisymSquare

namespace TauCeti

open antisymSquare

/-- For an abelian group `A`, the sequence `0 → A/2A → antisymSquare ℤ A → ⋀[ℤ]^2 A → 0` is
exact, stated through its maps: the comparison with the exterior square is a surjection
sending `a ∧ b` to `ιMulti ℤ 2 ![a, b]`, its kernel consists of the diagonal classes `a ∧ a`, and
two diagonal classes `a ∧ a` and `b ∧ b` agree exactly when `a - b ∈ 2A`. -/
theorem antisymSquare_diagonal_exact (A : Type*) [AddCommGroup A] :
    ∃ p : antisymSquare ℤ A →ₗ[ℤ] (⋀[ℤ]^2 A),
      Function.Surjective p ∧
      (∀ a b : A, p (Submodule.Quotient.mk (a ⊗ₜ[ℤ] b)) = exteriorPower.ιMulti ℤ 2 ![a, b]) ∧
      (∀ z : antisymSquare ℤ A, p z = 0 ↔ ∃ a : A,
        z = (Submodule.Quotient.mk (a ⊗ₜ[ℤ] a) : antisymSquare ℤ A)) ∧
      (∀ a b : A,
        (Submodule.Quotient.mk (a ⊗ₜ[ℤ] a) : antisymSquare ℤ A) =
          (Submodule.Quotient.mk (b ⊗ₜ[ℤ] b) : antisymSquare ℤ A) ↔
        ∃ c : A, a - b = 2 • c) := by
  refine ⟨toExterior ℤ A, toExterior_surjective, fun a b ↦ by simp, fun z ↦ ?_, fun a b ↦ ?_⟩
  · simp_rw [quotientMk_tmul, ← diag_apply, eq_comm (a := z)]
    exact exact_diag_toExterior z
  · simpa using mk_self_eq_mk_self_iff a b

end TauCeti
