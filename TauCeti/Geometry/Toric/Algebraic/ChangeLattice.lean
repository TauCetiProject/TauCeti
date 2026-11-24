/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.Algebra.MonoidAlgebra.Finite
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Finiteness
public import TauCeti.Geometry.Toric.Algebraic.FaceLocalization
public import TauCeti.Geometry.Toric.Algebraic.Normal

/-!
# Affine toric charts under a change of lattice

Let `i : N →+ V` and `i' : N' →+ V` be two integral lattices in the same real vector space and
`f : N' →+ N` a map of lattices compatible with them, `i' n = i (f n)`. Then the image of `f` has
finite index, and a cone `σ` is lattice rational for `N'` exactly when it is for `N`. Such a cone
has two dual semigroups `S = σ^∨ ∩ M` and `S' = σ^∨ ∩ M'`, for the character lattices
`M = N →+ ℤ` and `M' = N' →+ ℤ`. Restriction of characters along `f` maps `S` into `S'` and
induces the chart map `R[S] → R[S']`, that is, the toric morphism `U'_σ → U_σ` from the chart of
`σ` for the finite-index sublattice `N'` to its chart for `N` (so the character lattice `M'` is the
finer one). In rank one with `f = e •`, it is `q ↦ q'^e`.

The index `e` of `f` kills `N / f(N')`, so `e` times every character in `S'` is the restriction
of a character in `S`, and every monomial of `R[S']` is integral over `R[S]`. Since `S'` is
finitely generated for a lattice-rational cone (Gordan's lemma), `R[S']` is a finite
`R[S]`-module over every commutative ring `R`, without reducedness or noetherian hypotheses.
Over an integrally closed domain `R`, `R[S']` is moreover integrally closed, so it is the integral
closure of `R[S]` in the fraction field of `R[S']`.

Over `ℂ` the chart map is a finite morphism of affine toric schemes, and these morphisms commute
with the open immersions of faces, which are the maps along which the charts of a fan are glued.

## Main declarations

* `TauCeti.Toric.isLatticeRational_iff_of_comp`: lattice rationality of a cone is the same for
  both lattices.
* `TauCeti.Toric.mem_nsmulSaturation_mrange_dualSemigroupMap`: every character of `N'`
  nonnegative on `σ` has a positive multiple restricted from `N`.
* `TauCeti.Toric.finite_mapDomainRingHom_dualSemigroupMap`: the chart map `R[S] → R[S']` is
  finite over every commutative ring `R`.
* `TauCeti.Toric.isIntegralClosure_dualSemigroupMap`: over an integrally closed domain, `R[S']`
  is the integral closure of `R[S]` in the fraction field of `R[S']`.
* `TauCeti.Toric.isFinite_affineToricSchemeMap`: the morphism of complex affine toric charts is
  finite.
* `TauCeti.Toric.faceAffineToricSchemeMap_comp_affineToricSchemeMap`: these morphisms commute
  with face inclusions.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
* K.-W. Lan, *Integral models of toroidal compactifications with projective cone decompositions*,
  Int. Math. Res. Not. IMRN 2017, Construction 4.5 and Theorem 6.1(3)–(4).
* M. Dimitrov, *Compactifications arithmétiques des variétés de Hilbert et formes modulaires de
  Hilbert pour Γ₁(c, n)*, in *Geometric Aspects of Dwork Theory*, de Gruyter, 2004, Remarque 7.3.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric

variable {N N' V : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {i' : N' →+ V} {f : N' →+ N}

variable {σ : PointedCone ℝ V}

/-- A cone is lattice rational for a lattice exactly when it is lattice rational for a
compatible lattice in the same real vector space. -/
theorem isLatticeRational_iff_of_comp (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (hf : ∀ n, i' n = i (f n)) : IsLatticeRational i' σ ↔ IsLatticeRational i σ := by
  classical
  refine ⟨fun h ↦ by simpa using h.map (g := LinearMap.id) hf, fun h ↦ ?_⟩
  obtain ⟨s, rfl⟩ := isLatticeRational_iff.1 h
  refine isLatticeRational_iff.2 ?_
  have := hi.finiteIndex_range hi' hf
  -- Scale each generator by the index, which moves it into the image of `f`.
  have he : (0 : ℝ) < f.range.index := by exact_mod_cast f.range.index_pos
  choose g hg using fun n : N ↦ AddSubgroup.nsmul_index_mem f.range n
  have hig (n : N) : i' (g n) = (f.range.index : ℝ) • i n := by
    rw [hf, hg, map_nsmul, Nat.cast_smul_eq_nsmul]
  refine ⟨s.image g, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨n, hn, rfl⟩
    have : i n = (f.range.index : ℝ)⁻¹ • i' (g n) := by
      rw [hig, inv_smul_smul₀ he.ne']
    rw [this]
    exact Submodule.smul_mem _ ⟨_, (inv_pos.2 he).le⟩ (PointedCone.subset_hull
      (Set.mem_image_of_mem i' (Finset.mem_coe.2 (Finset.mem_image_of_mem g hn))))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨n', hn', rfl⟩
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hn'
    rw [hig]
    exact Submodule.smul_mem _ ⟨_, he.le⟩
      (PointedCone.subset_hull (Set.mem_image_of_mem i (Finset.mem_coe.2 hn)))

/-- Restricting characters along a compatible map `f : N' →+ N` sends the dual semigroup of a
cone for `N` to its dual semigroup for `N'`. Every character of `N'` nonnegative on the cone has
a positive multiple, namely its multiple by the index of `f`, in the image. -/
theorem mem_nsmulSaturation_mrange_dualSemigroupMap (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (hf : ∀ n, i' n = i (f n)) (m' : dualSemigroup hi' σ) :
    m' ∈ (AddMonoidHom.mrange
      (dualSemigroupMap hi' hi f LinearMap.id hf (Set.mapsTo_id (σ : Set V)))).nsmulSaturation := by
  have := hi.finiteIndex_range hi' hf
  set e := f.range.index
  choose g hg using fun n : N ↦ AddSubgroup.nsmul_index_mem f.range n
  -- The multiple `e • m'` of the real extension of `m'` is integral on `N`, since `e • n` lies in
  -- the image of `N'` for every `n : N`.
  obtain ⟨m, hm⟩ := (hi.exists_realCharacter_eq_iff (φ := e • hi'.realCharacter m')).2 fun n ↦
    ⟨(m' : N' →+ ℤ) (g n), by
      rw [LinearMap.smul_apply, ← map_nsmul, ← map_nsmul, ← hg, ← hf, hi'.realCharacter_apply]⟩
  have hmσ : m ∈ dualSemigroup hi σ := (mem_dualSemigroup hi m).2 fun x hx ↦ by
    rw [hm, LinearMap.smul_apply, nsmul_eq_mul]
    exact mul_nonneg (Nat.cast_nonneg _) ((mem_dualSemigroup hi' _).1 m'.property hx)
  refine AddSubmonoid.mem_nsmulSaturation.2 ⟨e, f.range.index_pos, ⟨m, hmσ⟩, Subtype.ext ?_⟩
  ext n'
  apply Int.cast_injective (α := ℝ)
  rw [coe_dualSemigroupMap, AddMonoidHom.comp_apply, ← hi.realCharacter_apply, ← hf, hm,
    LinearMap.smul_apply, hi'.realCharacter_apply]
  simp

/-- **Finiteness of affine toric charts under a change of lattice.** For a lattice-rational cone
`σ` and a compatible map `f : N' →+ N` of integral lattices in the same real vector space, the
chart map `R[σ^∨ ∩ M] → R[σ^∨ ∩ M']` induced by restricting characters along `f` is finite over
every commutative ring `R`. -/
theorem finite_mapDomainRingHom_dualSemigroupMap (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (hf : ∀ n, i' n = i (f n)) (hσ : IsLatticeRational i σ)
    (R : Type*) [CommRing R] :
    (AddMonoidAlgebra.mapDomainRingHom R
      (dualSemigroupMap hi' hi f LinearMap.id hf (Set.mapsTo_id (σ : Set V)))).Finite :=
  have := ((isLatticeRational_iff_of_comp hi hi' hf).2 hσ).fg_dualSemigroup hi'
  TauCeti.AddMonoidAlgebra.mapDomainRingHom_finite_of_forall_mem_nsmulSaturation _
    (mem_nsmulSaturation_mrange_dualSemigroupMap hi hi' hf) R

/-- **Normalization under a change of lattice.** Over an integrally closed domain `R`, for a
lattice-rational cone `σ` and a compatible map `f : N' →+ N` of integral lattices in the same
real vector space, `R[σ^∨ ∩ M']` is the integral closure of `R[σ^∨ ∩ M]` in any fraction field
`K` of `R[σ^∨ ∩ M']`, along the chart map followed by the localization map. -/
theorem isIntegralClosure_dualSemigroupMap (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (hf : ∀ n, i' n = i (f n)) (hσ : IsLatticeRational i σ)
    (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (K : Type*) [CommRing K]
    [Algebra (AddMonoidAlgebra R (dualSemigroup hi' σ)) K]
    [IsFractionRing (AddMonoidAlgebra R (dualSemigroup hi' σ)) K] :
    letI := ((algebraMap (AddMonoidAlgebra R (dualSemigroup hi' σ)) K).comp
      (AddMonoidAlgebra.mapDomainRingHom R
        (dualSemigroupMap hi' hi f LinearMap.id hf (Set.mapsTo_id (σ : Set V))))).toAlgebra
    IsIntegralClosure (AddMonoidAlgebra R (dualSemigroup hi' σ))
      (AddMonoidAlgebra R (dualSemigroup hi σ)) K := by
  let φ := AddMonoidAlgebra.mapDomainRingHom R
    (dualSemigroupMap hi' hi f LinearMap.id hf (Set.mapsTo_id (σ : Set V)))
  let := φ.toAlgebra
  let := ((algebraMap (AddMonoidAlgebra R (dualSemigroup hi' σ)) K).comp φ).toAlgebra
  have : IsScalarTower (AddMonoidAlgebra R (dualSemigroup hi σ))
      (AddMonoidAlgebra R (dualSemigroup hi' σ)) K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite (AddMonoidAlgebra R (dualSemigroup hi σ))
      (AddMonoidAlgebra R (dualSemigroup hi' σ)) :=
    finite_mapDomainRingHom_dualSemigroupMap hi hi' hf hσ R
  exact IsIntegralClosure.of_isIntegrallyClosed _ _ _

/-! ### Complex affine toric charts -/

section Scheme

universe u

variable {N N' : Type u} [AddCommGroup N] [AddCommGroup N'] {i : N →+ V} {i' : N' →+ V}
  {f : N' →+ N}

/-- **Finite toric morphism of a change of lattice.** For a lattice-rational cone `σ` and a
compatible map `f : N' →+ N` of integral lattices in the same real vector space, the morphism
from the complex affine toric chart of `σ` for `N'` to its chart for `N` is finite. -/
theorem isFinite_affineToricSchemeMap (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (hf : ∀ n, i' n = i (f n)) (hσ : IsLatticeRational i σ) :
    IsFinite (affineToricSchemeMap hi' hi f LinearMap.id hf (Set.mapsTo_id (σ : Set V))) := by
  have := ((isLatticeRational_iff_of_comp hi hi' hf).2 hσ).fg_dualSemigroup hi'
  rw [affineToricSchemeMap_def, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom,
    affineCoordinateRingMap_def]
  exact TauCeti.MonoidAlgebra.mapDomainRingHom_finite_of_forall_mem_powSaturation _
    (fun x ↦ (AddMonoidHom.mem_powSaturation_mrange_toMultiplicative _).2
      (mem_nsmulSaturation_mrange_dualSemigroupMap hi hi' hf x.toAdd)) ℂ

/-- Changing the lattice commutes with face inclusions: for a face `τ` of `σ`, the morphism of
complex affine toric charts of `τ` for `N'` into the chart of `σ` for `N` factors through the
chart of `σ` for `N'` and through the chart of `τ` for `N`. -/
theorem faceAffineToricSchemeMap_comp_affineToricSchemeMap {τ : PointedCone ℝ V}
    (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i') (hf : ∀ n, i' n = i (f n))
    (hτσ : τ.IsFaceOf σ) :
    faceAffineToricSchemeMap hi' hτσ ≫
        affineToricSchemeMap hi' hi f LinearMap.id hf (Set.mapsTo_id (σ : Set V)) =
      affineToricSchemeMap hi' hi f LinearMap.id hf (Set.mapsTo_id (τ : Set V)) ≫
        faceAffineToricSchemeMap hi hτσ := by
  simp only [faceAffineToricSchemeMap_eq_affineToricSchemeMap, affineToricSchemeMap_comp,
    AddMonoidHom.comp_id, AddMonoidHom.id_comp, LinearMap.id_comp]

end Scheme

end TauCeti.Toric
