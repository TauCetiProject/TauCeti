/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.AbelianScheme.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.MultiplicativeGroup

/-!
# The multiplicative group scheme is not proper

Over an affine scheme `S` whose ring of global sections is nonzero, the multiplicative group
scheme `𝔾_{m,S}` is not universally closed over `S`, hence not proper. If it were, its ring of
global sections would be integral over `Γ(S, 𝒪_S)` (Mathlib's
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`), in particular the universal unit
`u ∈ Γ(𝔾_{m,S}, 𝒪)ˣ`, the unit of the identity point. Every unit `a` of the global sections of a
scheme `T` over `S` is the image of `u` along the point `T ⟶ 𝔾_{m,S}` that `a` defines
(`TauCeti.GroupScheme.Gm.pointsMulEquiv_naturality`), so every such unit would be integral over
`Γ(S, 𝒪_S)` (`TauCeti.GroupScheme.Gm.isIntegralElem_of_universallyClosed`). The unit `T` of the
Laurent polynomial ring `Γ(S, 𝒪_S)[T, T⁻¹]` is not.

In particular `𝔾_m` over a field is not an abelian scheme
(`TauCeti.AlgebraicGeometry.AbelianScheme.toOver_ne_Gm`), although it is a smooth commutative group
scheme with geometrically connected fibres: properness is the axiom it fails.

## Main results

* `TauCeti.GroupScheme.Gm.not_universallyClosed`, `TauCeti.GroupScheme.Gm.not_isProper`:
  `𝔾_{m,S} ⟶ S` is neither universally closed nor proper for affine `S` with nonzero global
  sections.
* `TauCeti.GroupScheme.Gm.not_isProper_spec`: `𝔾_m` over `Spec R`, `R` a nonzero ring (for
  instance a field), is not proper.
* `TauCeti.AlgebraicGeometry.AbelianScheme.toOver_ne_Gm`: no abelian scheme over `Spec R` has
  `𝔾_m` as its underlying group scheme.
-/

public section

open CategoryTheory AlgebraicGeometry LaurentPolynomial Polynomial
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

namespace TauCeti.GroupScheme.Gm

/-- The unit `T` of the Laurent polynomial ring over a nonzero ring is not integral. -/
private theorem not_isIntegralElem_T (R : Type*) [CommRing R] [Nontrivial R] :
    ¬ (algebraMap R R[T;T⁻¹]).IsIntegralElem (T 1) := by
  rintro ⟨p, hp, h⟩
  have hc := congr_arg (fun f : R[T;T⁻¹] ↦ f.coeff (p.natDegree : ℤ)) h
  simp only [eval₂_eq_sum_range, T_pow, mul_one, ← LaurentPolynomial.C_eq_algebraMap,
    ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Nat.cast_inj] at hc
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 p.natDegree.lt_succ_self),
    hp.coeff_natDegree] at hc
  exact one_ne_zero hc

variable {S : Scheme.{u}}

/-- If `𝔾_{m,S}` is universally closed over an affine scheme `S`, then every unit of the global
sections of a scheme `U` over `S` is integral over `Γ(S, 𝒪_S)`: it is the image of the universal
unit, which is integral since the global sections of `𝔾_{m,S}` are. -/
theorem isIntegralElem_of_universallyClosed [IsAffine S] [UniversallyClosed (Gm S).X.hom]
    (U : Over S) (a : Γ(U.left, ⊤)ˣ) : U.hom.appTop.hom.IsIntegralElem (a : Γ(U.left, ⊤)) := by
  set x := (pointsMulEquiv U).symm a
  have hx : a = Units.map x.left.appTop.hom.toMonoidHom (pointsMulEquiv _ (𝟙 (Gm S).X)) := by
    rw [← pointsMulEquiv_naturality, Category.comp_id, MulEquiv.apply_symm_apply]
  have hu := isIntegral_appTop_of_universallyClosed (Gm S).X.hom
    (pointsMulEquiv _ (𝟙 (Gm S).X) : Γ((Gm S).X.left, ⊤))
  rw [hx, Units.coe_map]
  convert hu.map x.left.appTop.hom using 1
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, Over.w]

/-- **`𝔾_m` is not universally closed.** Over an affine scheme `S` whose ring of global sections
is nonzero, the structure morphism `𝔾_{m,S} ⟶ S` is not universally closed: otherwise the unit
`T` of `Γ(S, 𝒪_S)[T, T⁻¹]` would be integral over `Γ(S, 𝒪_S)`. -/
theorem not_universallyClosed [IsAffine S] [Nontrivial Γ(S, ⊤)] :
    ¬ UniversallyClosed (Gm S).X.hom := by
  intro h
  let R := Γ(S, ⊤)
  let φ : CommRingCat.of R ⟶ CommRingCat.of R[T;T⁻¹] := CommRingCat.ofHom (algebraMap R _)
  let T' : Over S := Over.mk (Spec.map φ ≫ S.isoSpec.inv)
  let a : Γ(T'.left, ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of R[T;T⁻¹])).inv.hom.toMonoidHom (isUnit_T 1).unit
  have hcomp : T'.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R[T;T⁻¹])).hom =
      (S.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ φ := by
    simp only [T', Over.mk_hom, Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality]
  have ha := (isIntegralElem_of_universallyClosed T' a).map
    (Scheme.ΓSpecIso (CommRingCat.of R[T;T⁻¹])).hom.hom
  rw [← CommRingCat.hom_comp, hcomp, CommRingCat.hom_comp] at ha
  apply not_isIntegralElem_T R
  convert RingHom.IsIntegralElem.of_comp ha using 1
  simp [a]

/-- **`𝔾_m` is not proper.** Over an affine scheme `S` whose ring of global sections is nonzero,
the structure morphism `𝔾_{m,S} ⟶ S` is not proper. -/
theorem not_isProper [IsAffine S] [Nontrivial Γ(S, ⊤)] : ¬ IsProper (Gm S).X.hom :=
  fun _ ↦ not_universallyClosed (S := S) inferInstance

/-- **`𝔾_m` over a nonzero ring is not proper**, for instance over a field. -/
theorem not_isProper_spec (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ IsProper (Gm (Spec (CommRingCat.of R))).X.hom :=
  have : Nontrivial Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  not_isProper

end TauCeti.GroupScheme.Gm

namespace TauCeti.AlgebraicGeometry.AbelianScheme

/-- **`𝔾_m` is not an abelian scheme.** Over `Spec R` for a nonzero ring `R`, for instance a field,
no abelian scheme has the multiplicative group scheme as its underlying group scheme, because
`𝔾_m` is not proper. -/
theorem toOver_ne_Gm (R : Type u) [CommRing R] [Nontrivial R]
    (A : AbelianScheme (Spec (CommRingCat.of R))) :
    A.toOver ≠ (GroupScheme.Gm (Spec (CommRingCat.of R))).X := fun h ↦
  GroupScheme.Gm.not_isProper_spec R (h ▸ A.isProper)

end TauCeti.AlgebraicGeometry.AbelianScheme
