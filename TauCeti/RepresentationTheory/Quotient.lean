/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RepresentationTheory.Basic
import TauCeti.GroupTheory.QuotientGroup.Basic
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Faithful quotient representations and factorization along surjections

Mathlib's `Representation.ofQuotient` descends a representation through a normal subgroup
acting trivially. The kernel always acts trivially, and quotienting by it gives a faithful
representation on the original module, with the caller's scalar and additive structures.
Likewise, a normal subgroup `N` acts trivially on the coset permutation module `R[G ⧸ N]`
(`Representation.instIsTrivialOfMulActionQuotientCompSubtype`). More generally, when the kernel of
a surjective group homomorphism `φ : G →* H` acts trivially, transporting `ofQuotient` across the
first isomorphism theorem factors the representation through `φ` (`Representation.ofSurjective`).

The kernel of the trivial representation is the whole group (`Representation.ker_trivial`), and
the kernel of a product is the intersection of the kernels (`Representation.ker_prod`).

## Main declarations

* `Representation.ker_trivial` and `Representation.ker_prod`: kernels of trivial and product
  representations.
* `Representation.isTrivial_comp_ker`: restriction to the kernel is trivial.
* `Representation.instIsTrivialOfMulActionQuotientCompSubtype`: a normal subgroup `N` acts
  trivially on `R[G ⧸ N]`.
* `Representation.ofQuotient_comp_mk'`: restricting `ofQuotient` along the quotient map recovers
  the original representation.
* `Representation.injective_ofQuotient_iff`: `ofQuotient` is faithful iff the subgroup is the
  entire kernel.
* `Representation.ofSurjective`: factor a representation through a surjective group homomorphism
  whose kernel acts trivially, with characteristic lemmas `Representation.ofSurjective_apply` and
  `Representation.ofSurjective_comp`.
-/

public section

namespace Representation

variable {R G M : Type*} [Semiring R] [Group G] [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M)

/-- The trivial representation has kernel the whole group. -/
@[simp]
theorem ker_trivial : (trivial R G M).ker = ⊤ :=
  MonoidHom.ker_one

/-- The kernel of a product is the intersection of the kernels. -/
@[simp]
theorem ker_prod {N : Type*} [AddCommMonoid N] [Module R N] (σ : Representation R G N) :
    (ρ.prod σ).ker = ρ.ker ⊓ σ.ker := by
  ext g
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker]
  refine ⟨fun h ↦ ⟨LinearMap.ext fun x ↦ congr_arg Prod.fst (LinearMap.congr_fun h (x, 0)),
    LinearMap.ext fun y ↦ congr_arg Prod.snd (LinearMap.congr_fun h (0, y))⟩,
    fun h ↦ LinearMap.ext fun x ↦ by simp [h.1, h.2]⟩

/-- Restriction to the kernel is a trivial representation. -/
instance isTrivial_comp_ker : IsTrivial (ρ.comp ρ.ker.subtype) where
  out g := MonoidHom.mem_ker.mp g.property

/-- For a normal subgroup `N` of `G`, the restriction of the coset permutation representation
`R[G ⧸ N]` to `N` is trivial. -/
instance instIsTrivialOfMulActionQuotientCompSubtype (N : Subgroup G) [N.Normal] :
    IsTrivial ((ofMulAction R G (G ⧸ N)).comp N.subtype) where
  out n := by
    ext x
    simp [TauCeti.smul_quotient_eq_self_of_mem n.property]

/-- Restricting a quotient representation along the quotient map recovers the original
representation, on the same module with the caller's scalar and additive structures. -/
@[simp]
theorem ofQuotient_comp_mk' (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] :
    (ρ.ofQuotient S).comp (QuotientGroup.mk' S) = ρ :=
  MonoidHom.ext fun g ↦ LinearMap.ext fun v ↦ ρ.ofQuotient_coe_apply S g v

/-- A quotient representation is faithful exactly when the subgroup removed is the entire
kernel. -/
theorem injective_ofQuotient_iff (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] :
    Function.Injective (ρ.ofQuotient S) ↔ S = ρ.ker := by
  have hS : S ≤ ρ.ker := fun g hg ↦
    MonoidHom.mem_ker.mpr (isTrivial_def (ρ.comp S.subtype) ⟨g, hg⟩)
  have h : ρ.ofQuotient S = QuotientGroup.lift S ρ hS := by
    ext q x
    simp
  rw [h, QuotientGroup.injective_lift_iff]

/-- Factor a representation through a surjective group homomorphism whose kernel acts
trivially. -/
noncomputable def ofSurjective {H : Type*} [Group H] (φ : G →* H) (hφ : Function.Surjective φ)
    [IsTrivial (ρ.comp φ.ker.subtype)] :
    Representation R H M :=
  (ρ.ofQuotient φ.ker).comp (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom

/-- Evaluating `ρ.ofSurjective φ hφ` on `φ g` recovers the action of `g`. -/
@[simp]
theorem ofSurjective_apply {H : Type*} [Group H] (φ : G →* H) (hφ : Function.Surjective φ)
    [IsTrivial (ρ.comp φ.ker.subtype)] (g : G) :
    ρ.ofSurjective φ hφ (φ g) = ρ g := by
  ext v
  simp [ofSurjective]

/-- Restricting `ρ.ofSurjective φ hφ` along `φ` recovers `ρ`. -/
@[simp]
theorem ofSurjective_comp {H : Type*} [Group H] (φ : G →* H) (hφ : Function.Surjective φ)
    [IsTrivial (ρ.comp φ.ker.subtype)] :
    (ρ.ofSurjective φ hφ).comp φ = ρ :=
  MonoidHom.ext (ρ.ofSurjective_apply φ hφ)

end Representation
