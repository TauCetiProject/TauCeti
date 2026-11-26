/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.ContinuousSMul
public import TauCeti.Geometry.Symplectic.Nonsqueezing.ProductCurve
public import TauCeti.Topology.ContinuousMap.UnparametrizedMap
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The one-marked moduli space of class-`A` spheres in `S² × M`

Gromov's proof of the nonsqueezing theorem counts pseudoholomorphic spheres in the class
`A = [S² × pt]` of a product `S² × M` of the Riemann sphere `OnePoint ℂ` with a manifold `M`,
through one marked point. A sphere `u : OnePoint ℂ → S² × M` in the torus case `M = T` lies in the
class `A` exactly when its sphere component `pr₁ ∘ u` has mapping degree one, since every sphere in
the torus is null-homotopic. This file defines, for any almost complex structure `J` on `S² × M`,
the **one-marked moduli space** `TauCeti.degreeOneMarkedSphereModuli J`: the one-marked
unparametrized spheres `[u, z]` (`TauCeti.MarkedUnparametrizedMap`, the quotient of pairs of a
nonconstant sphere and a point by the Möbius group `PSL(2, ℂ)`) represented by a smooth
`J`-holomorphic sphere `u` whose sphere component has degree one. The defining conditions do not
depend on the representative (`TauCeti.mk_mem_degreeOneMarkedSphereModuli_iff`): a Möbius
reparametrization is a holomorphic diffeomorphism of degree one.

For the product `J = i × K` of the complex structure of the sphere and an `ω_T`-tame almost
complex structure `K` on a torus `T`, such as the standard one, the class-`A` spheres are the
horizontal spheres `z ↦ (g • z, t)` (`TauCeti.degree_fst_comp_eq_one_iff_exists_smul`). So the
moduli space is the set of marked horizontal leaves `[y ↦ (y, t), w]`
(`TauCeti.degreeOneMarkedSphereModuli_prod_eq_range_horizontalLeaf`), and the evaluation map
`[u, z] ↦ u z` is a homeomorphism from it onto `S² × T`
(`TauCeti.degreeOneMarkedSphereModuliProdHomeomorph`): through every point of `S² × T` passes
exactly one class-`A` sphere, and the moduli space is compact
(`TauCeti.isCompact_degreeOneMarkedSphereModuli_prod`). Under this identification the one-marked
evaluation map is the identity of `S² × T`, the identification of the product-`J` evaluation that
the nonsqueezing argument starts from. Its degree `+1` additionally needs the orientation of the
moduli space, which is not constructed here.

## Main definitions

* `TauCeti.degreeOneMarkedSphereModuli J`: the one-marked moduli space of smooth `J`-holomorphic
  spheres in `S² × M` with sphere component of degree one.
* `TauCeti.degreeOneMarkedSphereModuliProdHomeomorph`: for a product structure on `S² × T`, the
  evaluation homeomorphism of the moduli space onto `S² × T`.

## Main results

* `TauCeti.mk_mem_degreeOneMarkedSphereModuli_iff`: membership of a class is a condition on any of
  its representatives.
* `TauCeti.degreeOneMarkedSphereModuli_prod_eq_range_horizontalLeaf`: for a product structure the
  moduli space consists of the marked horizontal leaves.
* `TauCeti.isCompact_degreeOneMarkedSphereModuli_prod`: for a product structure the moduli space
  is compact.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347, §0.3.A (the nonsqueezing theorem, proved through `S² × T^(2n-2)`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 9.3 (the proof of the nonsqueezing theorem, and the
  product-structure spheres of class `A` and their evaluation map).
-/

public section

noncomputable section

open Function Module Matrix
open scoped Manifold ContDiff MatrixGroups TauCeti.ComplexManifold

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

section Moduli

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The one-marked moduli space of degree-one spheres in `S² × M`.** For an almost complex
structure `J` on `S² × M`, the one-marked unparametrized spheres `[u, z]` represented by a smooth
`J`-holomorphic sphere `u : OnePoint ℂ → S² × M` whose sphere component `pr₁ ∘ u` has mapping
degree one, for the complex orientation of the Riemann sphere. For `M` a torus these are the
spheres of class `A = [S² × pt]`. -/
def degreeOneMarkedSphereModuli
    (J : SmoothAlmostComplexStructure (𝓘(ℝ, ℂ).prod I) (OnePoint ℂ × M)) :
    Set (MarkedUnparametrizedMap PSL(2, ℂ) (OnePoint ℂ) (OnePoint ℂ × M)) :=
  {x | ∃ (u : NonconstantMap (OnePoint ℂ) (OnePoint ℂ × M)) (z : OnePoint ℂ),
    Quotient.mk _ (u, z) = x ∧ ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod I) ∞ u ∧
      IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) J u ∧
      degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.fst ∘ u) = 1}

/-- Precomposing a smooth `J`-holomorphic sphere whose sphere component has degree one with a
Möbius transformation gives another such sphere. -/
private theorem comp_smul_of_degree_eq_one
    {J : SmoothAlmostComplexStructure (𝓘(ℝ, ℂ).prod I) (OnePoint ℂ × M)}
    {u : OnePoint ℂ → OnePoint ℂ × M} (hu : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod I) ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      J u)
    (hdeg : degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.fst ∘ u) = 1)
    (g : PSL(2, ℂ)) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod I) ∞ (u ∘ (g • ·)) ∧
      IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) J
        (u ∘ (g • ·)) ∧
      degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.fst ∘ (u ∘ (g • ·))) = 1 := by
  have hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (g • · : OnePoint ℂ → OnePoint ℂ) :=
    contMDiff_const_smul g
  have hfst : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (Prod.fst ∘ u) := contMDiff_fst.comp hu
  refine ⟨hu.comp hg, hhol.comp (isPseudoholomorphic_ofComplexManifold_iff.2
    ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ω) g).mdifferentiable (by simp))), ?_⟩
  -- The degree is multiplicative, and the Möbius transformation has degree one.
  rw [← comp_assoc, degree_comp _ _ _ hg hfst hg.continuous.isProperMap
    hfst.continuous.isProperMap, hdeg,
    ProjectiveSpecialLinearGroup.degree_reindex_complexManifoldOrientation_smul, mul_one]

/-- **Membership in the moduli space is a condition on any representative.** The class of a marked
sphere `(u, z)` lies in `degreeOneMarkedSphereModuli J` exactly when `u` itself is smooth,
`J`-holomorphic and has sphere component of degree one. -/
theorem mk_mem_degreeOneMarkedSphereModuli_iff
    {J : SmoothAlmostComplexStructure (𝓘(ℝ, ℂ).prod I) (OnePoint ℂ × M)}
    {u : NonconstantMap (OnePoint ℂ) (OnePoint ℂ × M)} {z : OnePoint ℂ} :
    Quotient.mk _ (u, z) ∈ degreeOneMarkedSphereModuli J ↔
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod I) ∞ u ∧
      IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) J u ∧
      degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.fst ∘ u) = 1 := by
  refine ⟨?_, fun h ↦ ⟨u, z, rfl, h⟩⟩
  rintro ⟨v, w, hvw, hv, hhol, hdeg⟩
  -- The representative `(v, w)` is `g • (u, z)`, so `u = v ∘ (g • ·)`.
  obtain ⟨g, hg⟩ : (v, w) ∈ MulAction.orbit PSL(2, ℂ) (u, z) := Quotient.exact hvw
  have hgu : g • u = v := congrArg Prod.fst hg
  have hu : ⇑u = v ∘ (g • ·) := funext fun y ↦ by
    rw [Function.comp_apply, ← hgu, NonconstantMap.smul_apply_smul]
  rw [hu]
  exact comp_smul_of_degree_eq_one hv hhol hdeg g

end Moduli

section Torus

variable {ι : Type*} [Fintype ι] {p : ι ⊕ ι → ℝ} [∀ i, Fact (0 < p i)]
  {K : SmoothAlmostComplexStructure (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
    (∀ i, AddCircle (p i))}

/-- **The class-`A` spheres of `S² × T` for a product structure are the horizontal leaves.** For
the product of the complex structure of the Riemann sphere and an `ω_T`-tame almost complex
structure `K` on the torus `T`, such as the standard one, the one-marked moduli space of degree-one
spheres consists of the marked horizontal leaves `[y ↦ (y, t), w]`. -/
theorem degreeOneMarkedSphereModuli_prod_eq_range_horizontalLeaf
    (hK : (torusSymplecticForm p).Tames K) :
    degreeOneMarkedSphereModuli ((SmoothAlmostComplexStructure.ofComplexManifold ℂ
      (OnePoint ℂ)).prod K) = Set.range (MarkedUnparametrizedMap.horizontalLeaf PSL(2, ℂ)) := by
  ext x
  induction x using Quotient.inductionOn with | h x =>
  obtain ⟨u, z⟩ := x
  rw [mk_mem_degreeOneMarkedSphereModuli_iff,
    MarkedUnparametrizedMap.mk_mem_range_horizontalLeaf_iff]
  constructor
  · rintro ⟨hu, hhol, hdeg⟩
    -- The sphere is `z ↦ (g • z, t)` for some `g ∈ GL(2, ℂ)`, which acts as an element of
    -- `PSL(2, ℂ)`.
    obtain ⟨g, t, hgt⟩ := (degree_fst_comp_eq_one_iff_exists_smul hu hK hhol).1 hdeg
    obtain ⟨h, hh⟩ := GeneralLinearGroup.exists_psl_forall_smul_eq_smul g
    exact ⟨h, t, fun y ↦ by rw [hh y]; exact congrFun hgt y⟩
  · rintro ⟨h, t, hu⟩
    induction h using QuotientGroup.induction_on with | H s =>
    have hu' : ⇑u = fun y ↦ ((s : GL (Fin 2) ℂ) • y, t) :=
      funext fun y ↦ by rw [hu y, OnePoint.pslMk_smul]
    have hsmooth := contMDiff_smul_prodMk_const (I' := ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
      (s : GL (Fin 2) ℂ) t
    have hhol := isPseudoholomorphic_smul_prodMk_const K (s : GL (Fin 2) ℂ) t
    rw [hu']
    exact ⟨hsmooth, hhol,
      (degree_fst_comp_eq_one_iff_exists_smul hsmooth hK hhol).2 ⟨_, t, rfl⟩⟩

/-- **The one-marked evaluation map for a product structure.** For the product of the complex
structure of the Riemann sphere and an `ω_T`-tame almost complex structure `K` on the torus `T`,
the evaluation `[u, z] ↦ u z` is a homeomorphism from the one-marked moduli space of degree-one
spheres onto `S² × T`: through every point of `S² × T` passes exactly one class-`A` sphere. -/
def degreeOneMarkedSphereModuliProdHomeomorph (hK : (torusSymplecticForm p).Tames K) :
    degreeOneMarkedSphereModuli ((SmoothAlmostComplexStructure.ofComplexManifold ℂ
      (OnePoint ℂ)).prod K) ≃ₜ OnePoint ℂ × ∀ i, AddCircle (p i) :=
  (Homeomorph.setCongr (degreeOneMarkedSphereModuli_prod_eq_range_horizontalLeaf hK)).trans
    (MarkedUnparametrizedMap.rangeHorizontalLeafHomeomorph _ _ _)

@[simp]
theorem degreeOneMarkedSphereModuliProdHomeomorph_apply (hK : (torusSymplecticForm p).Tames K)
    (x : degreeOneMarkedSphereModuli ((SmoothAlmostComplexStructure.ofComplexManifold ℂ
      (OnePoint ℂ)).prod K)) :
    degreeOneMarkedSphereModuliProdHomeomorph hK x = MarkedUnparametrizedMap.eval x.val :=
  MarkedUnparametrizedMap.rangeHorizontalLeafHomeomorph_apply _

@[simp]
theorem coe_degreeOneMarkedSphereModuliProdHomeomorph_symm_apply
    (hK : (torusSymplecticForm p).Tames K) (q : OnePoint ℂ × ∀ i, AddCircle (p i)) :
    ((degreeOneMarkedSphereModuliProdHomeomorph hK).symm q :
        MarkedUnparametrizedMap PSL(2, ℂ) (OnePoint ℂ) (OnePoint ℂ × ∀ i, AddCircle (p i))) =
      MarkedUnparametrizedMap.horizontalLeaf PSL(2, ℂ) q :=
  MarkedUnparametrizedMap.coe_rangeHorizontalLeafHomeomorph_symm_apply q

/-- **The class-`A` moduli space of a product structure is compact**, being homeomorphic to
`S² × T` through the evaluation map. -/
theorem isCompact_degreeOneMarkedSphereModuli_prod (hK : (torusSymplecticForm p).Tames K) :
    IsCompact (degreeOneMarkedSphereModuli ((SmoothAlmostComplexStructure.ofComplexManifold ℂ
      (OnePoint ℂ)).prod K)) :=
  isCompact_iff_compactSpace.2 (degreeOneMarkedSphereModuliProdHomeomorph hK).symm.compactSpace

end Torus

end TauCeti
