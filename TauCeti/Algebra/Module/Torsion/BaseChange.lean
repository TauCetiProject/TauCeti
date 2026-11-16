/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Algebra.Module.Torsion.Localization
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Localization

/-!
# Submonoid torsion under base change and tensor products

Let `R` be a commutative ring, `S` a submonoid of `R`, and `A` a localization of `R` at `S`.
Base change `A ⊗[R] -` is exact and kills a module exactly when it is `S`-torsion
(`Submonoid.isTorsion'_iff_subsingleton_tensorProduct`). Applied to the kernel and cokernel exact
sequences of an `R`-linear map `f : M →ₗ[R] N`, this characterizes when `f.baseChange A` is
injective, surjective, or bijective:

* `LinearMap.injective_baseChange_iff_isTorsion'_ker`: `f.baseChange A` is injective if and only
  if `LinearMap.ker f` is `S`-torsion.
* `LinearMap.surjective_baseChange_iff_isTorsion'_quotient`: `f.baseChange A` is surjective if and
  only if `N ⧸ LinearMap.range f` is `S`-torsion.
* `LinearMap.bijective_baseChange_iff`: `f.baseChange A` is bijective if and only if both the
  kernel and cokernel of `f` are `S`-torsion.

We also record the elementwise characterization of `S`-torsion quotients
(`Submodule.isTorsion'_quotient_iff`), uniform annihilation for finitely generated `S`-torsion
modules (`Module.IsTorsion'.exists_isTorsionBy_of_finite`), closure of `S`-torsion under tensor
products with arbitrary modules (`TauCeti.isTorsion'_tensorProduct_left`), and invertibility of
element orders of an `S`-torsion abelian group in a localization of `ℤ` at `S`
(`Submonoid.isUnit_addOrderOf_of_isTorsion'`).
-/

public section

open scoped TensorProduct

namespace Submodule

/-- A quotient module `N ⧸ p` is `S`-torsion if and only if every element of `N` is carried into
`p` by some element of `S`. -/
theorem isTorsion'_quotient_iff {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (p : Submodule R N) (S : Submonoid R) :
    Module.IsTorsion' (N ⧸ p) S ↔ ∀ y : N, ∃ s ∈ S, s • y ∈ p := by
  refine ⟨fun h y ↦ ?_, fun h q ↦ Submodule.Quotient.induction_on p q fun y ↦ ?_⟩
  · obtain ⟨⟨s, hs⟩, hsy⟩ := @h (Submodule.Quotient.mk y)
    exact ⟨s, hs, by simpa [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul] using hsy⟩
  · obtain ⟨s, hs, hsy⟩ := h y
    exact ⟨⟨s, hs⟩, by simpa [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul] using hsy⟩

end Submodule

namespace Module.IsTorsion'

/-- A finitely generated `S`-torsion module over a commutative semiring is uniformly annihilated by
a single element of `S`, namely the product of annihilators of a finite generating set. -/
theorem exists_isTorsionBy_of_finite {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {S : Submonoid R} [Module.Finite R M] (hM : Module.IsTorsion' M S) :
    ∃ s ∈ S, Module.IsTorsionBy R M s := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose s hs using fun g : G ↦ @hM g.1
  let r : R := ∏ g ∈ G.attach, (s g : R)
  refine ⟨r, S.prod_mem fun g _ ↦ (s g).2, ?_⟩
  rw [Module.isTorsionBy_iff_torsionBy_eq_top, eq_top_iff, ← hG, Submodule.span_le]
  intro x hx
  obtain ⟨c, hc⟩ :=
    Finset.dvd_prod_of_mem (fun g : G ↦ (s g : R)) (Finset.mem_attach G ⟨x, hx⟩)
  change r • x = 0
  rw [show r = (s ⟨x, hx⟩ : R) * c from hc, mul_comm, mul_smul,
    show (s ⟨x, hx⟩ : R) • x = 0 from hs ⟨x, hx⟩, smul_zero]

end Module.IsTorsion'

namespace TauCeti

/-- Tensoring an `S`-torsion module on the left with any module over a commuting base semiring
yields an `S`-torsion module. -/
theorem isTorsion'_tensorProduct_left {R R₀ M N : Type*} [CommSemiring R] [CommSemiring R₀]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Module R₀ M]
    [SMulCommClass R R₀ M] {S : Submonoid R₀} (hM : Module.IsTorsion' M S) :
    Module.IsTorsion' (M ⊗[R] N) S := fun t ↦ by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨s, hs⟩ := @hM x
    exact ⟨s, by rw [Submonoid.smul_def, TensorProduct.smul_tmul', ← Submonoid.smul_def, hs,
      TensorProduct.zero_tmul]⟩
  | add x y hx hy =>
    obtain ⟨s₁, hs₁⟩ := hx
    obtain ⟨s₂, hs₂⟩ := hy
    exact ⟨s₁ * s₂, by rw [smul_add, mul_smul, mul_smul, hs₂, smul_zero, add_zero, ← mul_smul,
      mul_comm, mul_smul, hs₁, smul_zero]⟩

end TauCeti

namespace LinearMap

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- Base change of `f : M →ₗ[R] N` to a localization `A` of `R` at `S` is injective if and only
if `LinearMap.ker f` is `S`-torsion. -/
theorem injective_baseChange_iff_isTorsion'_ker (f : M →ₗ[R] N) (S : Submonoid R) (A : Type*)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    Function.Injective (f.baseChange A) ↔ Module.IsTorsion' (LinearMap.ker f) S := by
  have : Module.Flat R A := IsLocalization.flat A S
  have hex : Function.Exact ((LinearMap.ker f).subtype.lTensor A) (f.lTensor A) :=
    Module.Flat.lTensor_exact A f.exact_subtype_ker_map
  have hinj : Function.Injective ((LinearMap.ker f).subtype.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [S.isTorsion'_iff_subsingleton_tensorProduct A]
  change Function.Injective (f.lTensor A) ↔ Subsingleton (A ⊗[R] LinearMap.ker f)
  rw [← LinearMap.ker_eq_bot, hex.linearMap_ker_eq, LinearMap.range_eq_bot]
  refine ⟨fun h ↦ subsingleton_of_forall_eq 0 fun x ↦ hinj ?_,
    fun _ ↦ LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  rw [map_zero]
  exact LinearMap.congr_fun h x

/-- Base change of `f : M →ₗ[R] N` to a localization `A` of `R` at `S` is surjective if and only
if the cokernel `N ⧸ LinearMap.range f` is `S`-torsion. -/
theorem surjective_baseChange_iff_isTorsion'_quotient (f : M →ₗ[R] N) (S : Submonoid R)
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A] :
    Function.Surjective (f.baseChange A) ↔ Module.IsTorsion' (N ⧸ LinearMap.range f) S := by
  have hex : Function.Exact (f.lTensor A) ((LinearMap.range f).mkQ.lTensor A) :=
    lTensor_exact A f.exact_map_mkQ_range (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective ((LinearMap.range f).mkQ.lTensor A) :=
    LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)
  rw [S.isTorsion'_iff_subsingleton_tensorProduct A]
  change Function.Surjective (f.lTensor A) ↔ Subsingleton (A ⊗[R] (N ⧸ LinearMap.range f))
  rw [← LinearMap.range_eq_top, ← hex.linearMap_ker_eq, LinearMap.ker_eq_top]
  refine ⟨fun h ↦ subsingleton_of_forall_eq 0 fun y ↦ ?_,
    fun _ ↦ LinearMap.ext fun _ ↦ Subsingleton.elim _ _⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact LinearMap.congr_fun h x

/-- Base change of `f : M →ₗ[R] N` to a localization `A` of `R` at `S` is bijective if and only
if both its kernel and its cokernel are `S`-torsion. -/
theorem bijective_baseChange_iff (f : M →ₗ[R] N) (S : Submonoid R) (A : Type*)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    Function.Bijective (f.baseChange A) ↔
      Module.IsTorsion' (LinearMap.ker f) S ∧ Module.IsTorsion' (N ⧸ LinearMap.range f) S :=
  and_congr (f.injective_baseChange_iff_isTorsion'_ker S A)
    (f.surjective_baseChange_iff_isTorsion'_quotient S A)

end LinearMap

namespace Submonoid

/-- If `S` is a submonoid of `ℤ`, `A` is a localization of `ℤ` at `S`, and `G` is an `S`-torsion
abelian group, then the additive order of every element of `G` is a unit in `A`. -/
theorem isUnit_addOrderOf_of_isTorsion' (S : Submonoid ℤ) (A : Type*)
    [CommRing A] [Algebra ℤ A] [IsLocalization S A] {G : Type*} [AddCommGroup G]
    (hG : Module.IsTorsion' G S) (a : G) : IsUnit (addOrderOf a : A) := by
  obtain ⟨⟨s, hs⟩, hsa⟩ := @hG a
  have hnsmul : s.natAbs • a = 0 := by
    rw [← natCast_zsmul]
    rcases Int.natAbs_eq s with h | h
    · exact h ▸ hsa
    · rw [← neg_eq_iff_eq_neg.2 h, neg_smul, show s • a = 0 from hsa, neg_zero]
  have hu : IsUnit (algebraMap ℤ A s) := IsLocalization.map_units A ⟨s, hs⟩
  refine isUnit_of_dvd_unit (Nat.cast_dvd_cast (addOrderOf_dvd_of_nsmul_eq_zero hnsmul)) ?_
  rcases Int.natAbs_eq s with h | h
  · simpa [← Int.cast_natCast (R := A), ← h] using hu
  · simpa [← Int.cast_natCast (R := A), ← neg_eq_iff_eq_neg.2 h] using hu.neg

end Submonoid
