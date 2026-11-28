/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic
public import TauCeti.AlgebraicGeometry.ResidueDegree
public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.AffineScheme.PrimesOver
import TauCeti.AlgebraicGeometry.Morphisms.CodimensionOne.Basic
import TauCeti.RingTheory.Length.Norm.PrimesOver

/-!
# The order of a norm at a point of codimension one

Let `f : X ⟶ Y` be a dominant morphism of locally Noetherian integral schemes, so that `f`
pulls back rational functions, `K(Y) → K(X)`. Let `y ∈ Y` be a point of codimension one with an
affine open neighbourhood `V` whose preimage `f⁻¹ V` is affine and finite over `V`. For a
rational function `r` on `X`,
`ord_y N_{K(X)/K(Y)}(r) = Σ_{f x = y} [κ(x) : κ(y)] ord_x(r)`
(`AlgebraicGeometry.Scheme.Hom.ord_norm_eq_finsum_of_isAffineOpen`). For nonzero `r`, this is the
coefficient of `div N(r)` at `y` in Fulton, *Intersection Theory*, Proposition 1.4(b): the
right-hand side is the coefficient at `y` of the pushforward of `div r` with residue-degree
weights. The theorem also includes `r = 0`, with Mathlib's convention that its orders vanish.

The proof reads the identity off the commutative algebra of Fulton's Appendix A.3
(`TauCeti.ordFrac_norm_eq_finprod_primesOver`) applied to the finite extension
`Γ(Y, V) → Γ(X, f⁻¹ V)`, the prime of `y` and the local rings of `X` at the points of the fibre,
which are the primes over it (`AlgebraicGeometry.IsAffineOpen.preimageSingletonEquivPrimesOver`).
The residue degrees enter as lengths: `length_{𝒪_{Y,y}} κ(x) = [κ(x) : κ(y)]`
(`AlgebraicGeometry.Scheme.Hom.toNat_length_residueField_eq_residueDegree`).

Adapted from the [lookahead formalization](https://github.com/roed-math/TauCeti-w2-fresh/tree/678c1bad7a8c53d6cffb49946b9fefc73d4c0435).
-/

public section

open AlgebraicGeometry CategoryTheory Order IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

variable [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

-- Convert the multiplicative local norm identity, indexed by primes, to the additive
-- identity indexed by points of the fibre. This also detects that the norm is nonzero.
private theorem ord_norm_eq_finsum_of_prod (f : X ⟶ Y) [IsDominant f] {y : Y}
    (hy1 : coheight y = 1) {I : Type u} [Fintype I] (e : (f ⁻¹' {y} : Set X) ≃ I)
    (r : X.functionField)
    (H : letI := f.functionFieldMap.hom.toAlgebra
      letI := krullDimLE_of_coheight_le hy1.le
      Ring.ordFrac (Y.presheaf.stalk y) (Algebra.norm Y.functionField r) =
        ∏ i, ((Multiplicative.ofAdd (f.residueDegree (e.symm i).val • X.ord r (e.symm i).val) :
          Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    letI := f.functionFieldMap.hom.toAlgebra
    Y.ord (Algebra.norm Y.functionField r) y =
      ∑ᶠ x ∈ f ⁻¹' {y}, X.ord r x * f.residueDegree x := by
  let _ := f.functionFieldMap.hom.toAlgebra
  let _ := krullDimLE_of_coheight_le hy1.le
  have hprod :
      ∏ i, ((Multiplicative.ofAdd (f.residueDegree (e.symm i).val • X.ord r (e.symm i).val) :
        Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ↑(∏ i, Multiplicative.ofAdd (f.residueDegree (e.symm i).val • X.ord r (e.symm i).val)) :=
    (map_prod (WithZero.coeMonoidHom : Multiplicative ℤ →* WithZero (Multiplicative ℤ)) _ _).symm
  rw [hprod, ← ofAdd_sum] at H
  have hN : Algebra.norm Y.functionField r ≠ 0 := by
    intro h0
    rw [h0, map_zero] at H
    exact WithZero.zero_ne_coe H
  -- `ordHom` is the stalk's `ordFrac`, with the dimension bound supplied by `hy1`.
  rw [Scheme.ord_eq_iff hy1 hN, Scheme.ordHom, ← finsum_set_coe_eq_finsum_mem,
    ← finsum_comp_equiv e.symm, finsum_eq_sum_of_fintype]
  refine H.trans ?_
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [nsmul_eq_mul, mul_comm]

-- The affine calculation keeps the chosen section, stalk and function-field algebras in one
-- scope: all the scalar towers passed to the ring-theoretic norm formula must use those same
-- structures. Its stages: (1) the finite extension `Γ(Y, V) → Γ(X, f⁻¹ V)` and the localization
-- `𝒪_{Y,y}` with its function-field towers; (2) the fibre points `x q` for primes `q` over `y`,
-- their stalks and stalk towers; (3) Fulton's Appendix A.3, rewritten into orders and residue
-- degrees. Codimension is supplied by `coheight_eq_one_of_isAffineOpen`; the lemma above
-- converts the multiplicative identity to an additive one.
private theorem ord_norm_eq_finsum_of_isAffineOpen_of_ne_zero
    (f : X ⟶ Y) [IsDominant f] {V : Y.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.Finite) {y : Y} (hy : y ∈ V)
    (hy1 : coheight y = 1) {r : X.functionField} (hr : r ≠ 0) :
    letI := f.functionFieldMap.hom.toAlgebra
    Y.ord (Algebra.norm Y.functionField r) y =
      ∑ᶠ x ∈ f ⁻¹' {y}, X.ord r x * f.residueDegree x := by
  let _ := f.functionFieldMap.hom.toAlgebra
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  -- The finite extension `A₀ = Γ(Y, V) → B₀ = Γ(X, f⁻¹ V)` of domains.
  algebraize [(f.appLE V (f ⁻¹ᵁ V) le_rfl).hom]
  set p := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  -- The local ring `A = 𝒪_{Y,y}` is the localization of `A₀` at `p`.
  let _ : Algebra Γ(Y, V) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) p := hV.isLocalization_stalk ⟨y, hy⟩
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le hy1.le
  -- The function fields and their towers.
  let _ : Algebra (Y.presheaf.stalk y) X.functionField :=
    ((algebraMap Y.functionField X.functionField).comp
      (algebraMap (Y.presheaf.stalk y) Y.functionField)).toAlgebra
  have : IsScalarTower (Y.presheaf.stalk y) Y.functionField X.functionField :=
    .of_algebraMap_eq' rfl
  let _ : Algebra Γ(Y, V) X.functionField :=
    ((algebraMap (Y.presheaf.stalk y) X.functionField).comp
      (algebraMap Γ(Y, V) (Y.presheaf.stalk y))).toAlgebra
  have : IsScalarTower Γ(Y, V) (Y.presheaf.stalk y) X.functionField := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) X.functionField :=
    .of_algebraMap_eq' (f.functionFieldMap_comp_algebraMap_comp_germ V (f ⁻¹ᵁ V) le_rfl hy)
  have : IsFractionRing Γ(X, f ⁻¹ᵁ V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X _ hU
  -- The points of the fibre, indexed by the primes of `B₀` over `p`.
  let x (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : X := hU.fromSpec ⟨q.val, q.property.1⟩
  have hxU (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : x q ∈ f ⁻¹ᵁ V := hU.fromSpec_mem _
  let e := hV.preimageSingletonEquivPrimesOver f hU rfl hy
  have hex (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : (e.symm q).val = x q :=
    hV.coe_preimageSingletonEquivPrimesOver_symm_apply f hU rfl hy q
  have hfx (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : f (x q) = y := hex q ▸ (e.symm q).property
  -- The local rings `𝒪_{X, x q}`, localizations of `B₀` at `q` and `A`-algebras.
  let _ (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Algebra Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk (x q)) :=
    X.presheaf.algebra_section_stalk ⟨x q, hxU q⟩
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : IsLocalization.AtPrime (X.presheaf.stalk (x q)) q.val :=
    hU.isLocalization_stalk' ⟨q.val, q.property.1⟩ (hxU q)
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) :
      IsScalarTower Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk (x q)) X.functionField :=
    functionField_isScalarTower X (f ⁻¹ᵁ V) ⟨x q, hxU q⟩
  let _ (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Algebra (Y.presheaf.stalk y) (X.presheaf.stalk (x q)) :=
    f.stalkAlgebraOfApplyEq (hfx q)
  let _ (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Algebra Γ(Y, V) (X.presheaf.stalk (x q)) :=
    ((algebraMap Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk (x q))).comp
      (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V))).toAlgebra
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) :
      IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk (x q)) :=
    .of_algebraMap_eq' rfl
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) :
      IsScalarTower Γ(Y, V) (Y.presheaf.stalk y) (X.presheaf.stalk (x q)) :=
    .of_algebraMap_eq' (f.algebraMap_stalkAlgebraOfApplyEq_comp_germ V (f ⁻¹ᵁ V) le_rfl
      (hfx q) (hxU q) hy).symm
  have hq1 (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : coheight (x q) = 1 :=
    coheight_eq_one_of_isAffineOpen f hV hU hfin hy hy1 (hfx q)
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Ring.KrullDimLE 1 (X.presheaf.stalk (x q)) :=
    krullDimLE_of_coheight_le (hq1 q).le
  -- Fulton's Appendix A.3 over the primes above `p`.
  have H := TauCeti.ordFrac_norm_eq_finprod_primesOver
    (K := Y.functionField) (A := Y.presheaf.stalk y) p
    (fun q ↦ X.presheaf.stalk (x q)) hr
  have hord (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Ring.ordFrac (X.presheaf.stalk (x q)) r =
      ↑(Multiplicative.ofAdd (X.ord r (x q))) := by
    -- Explicitly unfold `ordHom` to the stalk's `ordFrac`, with dimension bound from `hq1`.
    simpa only [Scheme.ordHom] using
      (Scheme.ord_eq_iff (hq1 q) hr (n := X.ord r (x q))).mp rfl
  have : Fintype (p.primesOver Γ(X, f ⁻¹ᵁ V)) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  simp only [hord, Scheme.Hom.toNat_length_residueField_eq_residueDegree f (hfx _),
    ← WithZero.coe_pow, ← ofAdd_nsmul, finprod_eq_prod_of_fintype] at H
  apply ord_norm_eq_finsum_of_prod f hy1 e r
  simpa only [hex] using H

/-- **The order of a norm at a point of codimension one** (Fulton, *Intersection Theory*,
Proposition 1.4(b) and Appendix A.3). Let `f : X ⟶ Y` be a dominant morphism of locally
Noetherian integral schemes, `y ∈ Y` a point of codimension one, and `V ∋ y` an affine open whose
preimage is affine and finite over it. For a rational function `r` on `X`,
`ord_y N_{K(X)/K(Y)}(r) = Σ_{f x = y} [κ(x) : κ(y)] ord_x(r)`. -/
theorem ord_norm_eq_finsum_of_isAffineOpen (f : X ⟶ Y) [IsDominant f] {V : Y.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.Finite) {y : Y} (hy : y ∈ V)
    (hy1 : coheight y = 1) (r : X.functionField) :
    letI := f.functionFieldMap.hom.toAlgebra
    Y.ord (Algebra.norm Y.functionField r) y =
      ∑ᶠ x ∈ f ⁻¹' {y}, X.ord r x * f.residueDegree x := by
  let _ := f.functionFieldMap.hom.toAlgebra
  rcases eq_or_ne r 0 with rfl | hr
  · by_cases h : Module.Finite Y.functionField X.functionField
    · have := h
      simp
    · simp [Algebra.norm_eq_one_of_not_module_finite h]
  · exact ord_norm_eq_finsum_of_isAffineOpen_of_ne_zero f hV hU hfin hy hy1 hr

end AlgebraicGeometry.Scheme.Hom
