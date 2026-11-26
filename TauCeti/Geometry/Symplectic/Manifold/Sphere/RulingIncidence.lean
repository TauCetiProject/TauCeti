/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.DistinctTriples
public import TauCeti.Geometry.Symplectic.Manifold.Sphere.ProductCurve
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup.RotationGroup
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Incident pairs of ruling spheres in `S² × S²` for the product structure

Let `S² = OnePoint ℂ` be the Riemann sphere and `p₀` a point of it. For an almost complex structure
`J` on `S² × S²`, the **incidence space** `TauCeti.rulingIncidence J p₀` consists of the pairs
`(u, v)` of smooth `J`-holomorphic spheres `u, v : S² → S² × S²` such that `u` parametrizes a
sphere of the ruling class `A = [S² × pt]`, `v` one of the ruling class `B = [pt × S²]`, and the
two parametrizations agree at the base point, `u p₀ = v p₀`. The classes are read off the
component degrees, `(1, 0)` for `A` and `(0, 1)` for `B`, which are the coordinates of the
homology class of a sphere in the basis `A`, `B`. As `J` varies over the tame almost complex
structures, these spaces are the fibres of the space of incident ruling parametrizations through
which the symplectomorphism group of equal-area `S² × S²` is compared with
`SO(3) × SO(3)`. The spaces of maps carry the compact-open topology.

This file computes the fibre for the product `J₀ = i × i` of the complex structures of the two
factors. By `TauCeti.degree_fst_comp_eq_one_and_degree_snd_comp_eq_zero_iff_exists_smul` and its
companion for `B`, the `J₀`-holomorphic spheres of the two classes are the horizontal spheres
`z ↦ (a • z, w)` and the vertical spheres `z ↦ (w, b • z)` for Möbius transformations `a`, `b`.
The incidence condition fixes the two constant coordinates, so the fibre is parametrized by pairs
`(a, b)` of elements of `PSL(2, ℂ)` through

`(a, b) ↦ (z ↦ (a • z, b • p₀), w ↦ (a • p₀, b • w))`

(`TauCeti.rulingLeafPair`, `TauCeti.rulingIncidence_prod_eq_range`). The parametrization is
injective, since `PSL(2, ℂ)` acts faithfully on the sphere, and it is a homeomorphism onto the
fibre (`TauCeti.pslProdHomeomorphRulingIncidence`): its inverse recovers `a` and `b` from the
values of the two spheres at `0`, `1` and `∞`, through the homeomorphism
`OnePoint.pslHomeomorphDistinctTriples` of `PSL(2, ℂ)` with the ordered triples of distinct
points. Since `PSL(2, ℂ)` deformation retracts onto its rotation subgroup `PSU(2) ≅ SO(3)`
(`TauCeti.pslHomotopyEquivSO3`), the fibre is homotopy equivalent to `SO(3) × SO(3)`
(`TauCeti.rulingIncidenceHomotopyEquiv`), whose homotopy inverse sends a pair of rotations to the
pair of rotated leaves.

Two actions of `PSL(2, ℂ) × PSL(2, ℂ)` are visible in this parametrization. The product
`k₁ × k₂` of two Möbius transformations is a biholomorphism of `S² × S²`, and composing both
spheres with it multiplies the parameter on the left (`TauCeti.rulingLeafPair_mul_fst_apply`,
`TauCeti.rulingLeafPair_mul_snd_apply`). Reparametrizing the two spheres independently does not
preserve the incidence condition: `(u ∘ k₁, v ∘ k₂)` lies in the fibre again exactly when both
`k₁` and `k₂` fix the base point (`TauCeti.comp_smul_mem_rulingIncidence_prod_iff`), and then it
is the parametrization of the right product by `(k₁, k₂)`
(`TauCeti.rulingLeafPair_mul_fst_apply_of_smul_eq`,
`TauCeti.rulingLeafPair_mul_snd_apply_of_smul_eq`). So reparametrizations act on the fibre only
through the stabilizers of the base point.

## Main definitions

* `TauCeti.rulingIncidence J p₀`: the pairs of a class-`A` and a class-`B` smooth
  `J`-holomorphic sphere agreeing at `p₀`.
* `TauCeti.rulingLeafPair p₀ (a, b)`: the pair `(z ↦ (a • z, b • p₀), w ↦ (a • p₀, b • w))`.
* `TauCeti.pslProdHomeomorphRulingIncidence p₀`: for the product structure, the homeomorphism
  `PSL(2, ℂ) × PSL(2, ℂ) ≃ₜ rulingIncidence J₀ p₀` given by `rulingLeafPair`.
* `TauCeti.rulingIncidenceHomotopyEquiv p₀`: for the product structure, the homotopy equivalence
  of the fibre with `SO(3) × SO(3)`.

## Main results

* `TauCeti.rulingIncidence_prod_eq_range`: for the product structure, the fibre is the range of
  `rulingLeafPair p₀`.
* `TauCeti.rulingLeafPair_injective`: the parametrization is injective.
* `TauCeti.comp_smul_mem_rulingIncidence_prod_iff`: independent reparametrizations preserve the
  fibre exactly when they fix the base point.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347, §2.4 (the rulings of `S² × S²` and its symplectomorphism group).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 9.5 (the symplectomorphism group of `S² × S²`).
-/

public section

noncomputable section

open Function Module Matrix Set
open scoped Manifold ContDiff ContinuousMap MatrixGroups TauCeti.ComplexManifold

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

/-! ### The incidence space -/

/-- **The incidence space of the two rulings of `S² × S²`.** For an almost complex structure `J` on
`S² × S²` and a base point `p₀` of the Riemann sphere, the pairs `(u, v)` of smooth `J`-holomorphic
spheres such that `u` has component degrees `(1, 0)`, so lies in the ruling class `A = [S² × pt]`,
`v` has component degrees `(0, 1)`, so lies in the ruling class `B = [pt × S²]`, and
`u p₀ = v p₀`. -/
def rulingIncidence
    (J : SmoothAlmostComplexStructure (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) (OnePoint ℂ × OnePoint ℂ))
    (p₀ : OnePoint ℂ) :
    Set (C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ) × C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ)) :=
  {e | (ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ e.1 ∧
      IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) J e.1 ∧
      degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.fst ∘ e.1) = 1 ∧
      degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.snd ∘ e.1) = 0) ∧
    (ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ e.2 ∧
      IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) J e.2 ∧
      degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.fst ∘ e.2) = 0 ∧
      degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.snd ∘ e.2) = 1) ∧
    e.1 p₀ = e.2 p₀}

/-- Membership in the incidence space `TauCeti.rulingIncidence J p₀`: a smooth `J`-holomorphic
sphere of class `A`, a smooth `J`-holomorphic sphere of class `B`, and agreement at `p₀`. -/
theorem mem_rulingIncidence_iff
    {J : SmoothAlmostComplexStructure (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) (OnePoint ℂ × OnePoint ℂ)}
    {p₀ : OnePoint ℂ}
    {e : C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ) × C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ)} :
    e ∈ rulingIncidence J p₀ ↔
      (ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ e.1 ∧
        IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) J e.1 ∧
        degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
            (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
            (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          (Prod.fst ∘ e.1) = 1 ∧
        degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
            (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
            (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          (Prod.snd ∘ e.1) = 0) ∧
      (ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ e.2 ∧
        IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) J e.2 ∧
        degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
            (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
            (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          (Prod.fst ∘ e.2) = 0 ∧
        degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
            (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
            (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          (Prod.snd ∘ e.2) = 1) ∧
      e.1 p₀ = e.2 p₀ :=
  Iff.rfl

/-! ### The parametrization by pairs of Möbius transformations -/

/-- **The pair of leaves parametrized by two Möbius transformations.** For a base point `p₀` and
`(a, b)` in `PSL(2, ℂ) × PSL(2, ℂ)`, the horizontal sphere `z ↦ (a • z, b • p₀)` and the vertical
sphere `w ↦ (a • p₀, b • w)`, which both pass through `(a • p₀, b • p₀)` at `p₀`. -/
def rulingLeafPair (p₀ : OnePoint ℂ) (g : PSL(2, ℂ) × PSL(2, ℂ)) :
    C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ) × C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ) :=
  (⟨fun z ↦ (g.1 • z, g.2 • p₀), (continuous_const_smul g.1).prodMk continuous_const⟩,
    ⟨fun w ↦ (g.1 • p₀, g.2 • w), continuous_const.prodMk (continuous_const_smul g.2)⟩)

@[simp]
theorem rulingLeafPair_fst_apply (p₀ : OnePoint ℂ) (g : PSL(2, ℂ) × PSL(2, ℂ)) (z : OnePoint ℂ) :
    (rulingLeafPair p₀ g).1 z = (g.1 • z, g.2 • p₀) :=
  (rfl)

@[simp]
theorem rulingLeafPair_snd_apply (p₀ : OnePoint ℂ) (g : PSL(2, ℂ) × PSL(2, ℂ)) (w : OnePoint ℂ) :
    (rulingLeafPair p₀ g).2 w = (g.1 • p₀, g.2 • w) :=
  (rfl)

/-- **The parametrization is injective**, since `PSL(2, ℂ)` acts faithfully on the Riemann
sphere: the first sphere determines `a`, and the second determines `b`. -/
theorem rulingLeafPair_injective (p₀ : OnePoint ℂ) : Injective (rulingLeafPair p₀) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have ha : a = a' := eq_of_smul_eq_smul fun z ↦
    congrArg Prod.fst (DFunLike.congr_fun (congrArg Prod.fst h) z)
  have hb : b = b' := eq_of_smul_eq_smul fun w ↦
    congrArg Prod.snd (DFunLike.congr_fun (congrArg Prod.snd h) w)
  rw [ha, hb]

/-- The parametrization is continuous for the compact-open topology, since the Möbius action is
jointly continuous. -/
theorem continuous_rulingLeafPair (p₀ : OnePoint ℂ) : Continuous (rulingLeafPair p₀) :=
  (ContinuousMap.continuous_of_continuous_uncurry _
      ((continuous_fst.fst.smul continuous_snd).prodMk
        (continuous_fst.snd.smul continuous_const))).prodMk
    (ContinuousMap.continuous_of_continuous_uncurry _
      ((continuous_fst.fst.smul continuous_const).prodMk
        (continuous_fst.snd.smul continuous_snd)))

/-- **Left multiplication is composition with a product of Möbius transformations**: the first
sphere of `rulingLeafPair p₀ (k * g)` is the first sphere of `rulingLeafPair p₀ g` followed by the
biholomorphism `k₁ × k₂` of `S² × S²`. -/
theorem rulingLeafPair_mul_fst_apply (p₀ : OnePoint ℂ) (k g : PSL(2, ℂ) × PSL(2, ℂ))
    (z : OnePoint ℂ) :
    (rulingLeafPair p₀ (k * g)).1 z = Prod.map (k.1 • ·) (k.2 • ·) ((rulingLeafPair p₀ g).1 z) := by
  simp [mul_smul]

/-- **Left multiplication is composition with a product of Möbius transformations**: the second
sphere of `rulingLeafPair p₀ (k * g)` is the second sphere of `rulingLeafPair p₀ g` followed by the
biholomorphism `k₁ × k₂` of `S² × S²`. -/
theorem rulingLeafPair_mul_snd_apply (p₀ : OnePoint ℂ) (k g : PSL(2, ℂ) × PSL(2, ℂ))
    (w : OnePoint ℂ) :
    (rulingLeafPair p₀ (k * g)).2 w = Prod.map (k.1 • ·) (k.2 • ·) ((rulingLeafPair p₀ g).2 w) := by
  simp [mul_smul]

/-- **Right multiplication by the stabilizer reparametrizes the first sphere**: if `k₂` fixes `p₀`,
the first sphere of `rulingLeafPair p₀ (g * k)` is that of `rulingLeafPair p₀ g` precomposed with
`k₁`. -/
theorem rulingLeafPair_mul_fst_apply_of_smul_eq (p₀ : OnePoint ℂ) (g k : PSL(2, ℂ) × PSL(2, ℂ))
    (hk : k.2 • p₀ = p₀) (z : OnePoint ℂ) :
    (rulingLeafPair p₀ (g * k)).1 z = (rulingLeafPair p₀ g).1 (k.1 • z) := by
  simp [mul_smul, hk]

/-- **Right multiplication by the stabilizer reparametrizes the second sphere**: if `k₁` fixes
`p₀`, the second sphere of `rulingLeafPair p₀ (g * k)` is that of `rulingLeafPair p₀ g`
precomposed with `k₂`. -/
theorem rulingLeafPair_mul_snd_apply_of_smul_eq (p₀ : OnePoint ℂ) (g k : PSL(2, ℂ) × PSL(2, ℂ))
    (hk : k.1 • p₀ = p₀) (w : OnePoint ℂ) :
    (rulingLeafPair p₀ (g * k)).2 w = (rulingLeafPair p₀ g).2 (k.2 • w) := by
  simp [mul_smul, hk]

/-! ### The fibre for the product structure -/

/-- **The parametrized pairs of leaves are incident ruling spheres for the product structure.** -/
theorem rulingLeafPair_mem_rulingIncidence (p₀ : OnePoint ℂ) (g : PSL(2, ℂ) × PSL(2, ℂ)) :
    rulingLeafPair p₀ g ∈ rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ
      (OnePoint ℂ)).prod (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀ := by
  obtain ⟨a, b⟩ := g
  induction a using QuotientGroup.induction_on with | H s => ?_
  induction b using QuotientGroup.induction_on with | H t => ?_
  -- Both spheres are Möbius transformations of `GL(2, ℂ)` paired with a constant.
  have hu : ⇑(rulingLeafPair p₀ (s, t)).1 =
      fun z ↦ ((s : GL (Fin 2) ℂ) • z, ((t : PSL(2, ℂ)) • p₀)) :=
    funext fun z ↦ by simp only [rulingLeafPair_fst_apply, OnePoint.pslMk_smul]
  have hv : ⇑(rulingLeafPair p₀ (s, t)).2 =
      fun w ↦ ((s : PSL(2, ℂ)) • p₀, (t : GL (Fin 2) ℂ) • w) :=
    funext fun w ↦ by simp only [rulingLeafPair_snd_apply, OnePoint.pslMk_smul]
  have huhol := isPseudoholomorphic_smul_prodMk_const
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) (s : GL (Fin 2) ℂ)
    ((t : PSL(2, ℂ)) • p₀)
  have hvhol := isPseudoholomorphic_const_prodMk_smul
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) ((s : PSL(2, ℂ)) • p₀)
    (t : GL (Fin 2) ℂ)
  rw [mem_rulingIncidence_iff, hu, hv]
  exact ⟨⟨contMDiff_smul_prodMk_const _ _, huhol,
      (degree_fst_comp_eq_one_and_degree_snd_comp_eq_zero_iff_exists_smul huhol).2 ⟨_, _, rfl⟩⟩,
    ⟨contMDiff_const_prodMk_smul _ _, hvhol,
      (degree_fst_comp_eq_zero_and_degree_snd_comp_eq_one_iff_exists_smul hvhol).2 ⟨_, _, rfl⟩⟩,
    by simp only [OnePoint.pslMk_smul]⟩

/-- **The fibre of the incidence space for the product structure.** For the product `J₀ = i × i`
of the complex structures of the two factors, the incident pairs of ruling spheres are exactly the
pairs `(z ↦ (a • z, b • p₀), w ↦ (a • p₀, b • w))` for `a`, `b` in `PSL(2, ℂ)`. -/
theorem rulingIncidence_prod_eq_range (p₀ : OnePoint ℂ) :
    rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀ =
      range (rulingLeafPair p₀) := by
  refine Subset.antisymm ?_ (range_subset_iff.2 (rulingLeafPair_mem_rulingIncidence p₀))
  rintro ⟨u, v⟩ ⟨⟨-, huhol, hu₁, hu₂⟩, ⟨-, hvhol, hv₁, hv₂⟩, hp⟩
  -- The class-`A` sphere is horizontal and the class-`B` sphere vertical, for Möbius
  -- transformations of `GL(2, ℂ)`, which act as elements of `PSL(2, ℂ)`.
  obtain ⟨g, w, hg⟩ :=
    (degree_fst_comp_eq_one_and_degree_snd_comp_eq_zero_iff_exists_smul huhol).1 ⟨hu₁, hu₂⟩
  obtain ⟨w', h, hh⟩ :=
    (degree_fst_comp_eq_zero_and_degree_snd_comp_eq_one_iff_exists_smul hvhol).1 ⟨hv₁, hv₂⟩
  obtain ⟨a, ha⟩ := GeneralLinearGroup.exists_psl_forall_smul_eq_smul g
  obtain ⟨b, hb⟩ := GeneralLinearGroup.exists_psl_forall_smul_eq_smul h
  -- The incidence `u p₀ = v p₀` determines the two constant coordinates.
  have hp' : (g • p₀, w) = (w', h • p₀) := by
    rw [← congrFun hg p₀, ← congrFun hh p₀]
    exact hp
  obtain ⟨hw', hw⟩ := Prod.mk.inj hp'
  refine ⟨(a, b), Prod.ext (ContinuousMap.ext fun z ↦ ?_) (ContinuousMap.ext fun z ↦ ?_)⟩
  · rw [rulingLeafPair_fst_apply, congrFun hg z, ha, hb, hw]
  · rw [rulingLeafPair_snd_apply, congrFun hh z, ha, hb, hw']

/-- **Independent reparametrizations preserve the fibre exactly when they fix the base point.** For
an incident pair `(u, v)` of ruling spheres of the product structure and Möbius transformations
`k₁`, `k₂`, the reparametrized pair `(u ∘ k₁, v ∘ k₂)` is again incident exactly when `k₁` and `k₂`
both fix `p₀`. -/
theorem comp_smul_mem_rulingIncidence_prod_iff {p₀ : OnePoint ℂ}
    {e : C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ) × C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ)}
    (he : e ∈ rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ
      (OnePoint ℂ)).prod (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀)
    (k : PSL(2, ℂ) × PSL(2, ℂ)) :
    (e.1.comp ⟨(k.1 • ·), continuous_const_smul k.1⟩,
        e.2.comp ⟨(k.2 • ·), continuous_const_smul k.2⟩) ∈
        rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
          (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀ ↔
      k.1 • p₀ = p₀ ∧ k.2 • p₀ = p₀ := by
  rw [rulingIncidence_prod_eq_range] at he ⊢
  obtain ⟨g, rfl⟩ := he
  constructor
  · -- The reparametrized spheres pass through `(g₁ k₁ • p₀, g₂ • p₀)` and `(g₁ • p₀, g₂ k₂ • p₀)`
    -- at `p₀`, and these agree only if `k₁` and `k₂` fix `p₀`.
    rintro ⟨g', hg'⟩
    have h := (DFunLike.congr_fun (congrArg Prod.fst hg') p₀).symm.trans
      (DFunLike.congr_fun (congrArg Prod.snd hg') p₀)
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, rulingLeafPair_fst_apply,
      rulingLeafPair_snd_apply, Prod.mk.injEq] at h
    exact ⟨smul_left_cancel g.1 h.1, (smul_left_cancel g.2 h.2).symm⟩
  · rintro ⟨hk₁, hk₂⟩
    refine ⟨g * k, Prod.ext (ContinuousMap.ext fun z ↦ ?_) (ContinuousMap.ext fun w ↦ ?_)⟩
    · exact rulingLeafPair_mul_fst_apply_of_smul_eq p₀ g k hk₂ z
    · exact rulingLeafPair_mul_snd_apply_of_smul_eq p₀ g k hk₁ w

/-! ### The fibre is homeomorphic to `PSL(2, ℂ) × PSL(2, ℂ)` -/

/-- **A continuous inverse of the parametrization.** The Möbius transformations `a` and `b` are
recovered continuously from an incident pair, through the values of its two spheres at `0`, `1`
and `∞`: these are ordered triples of distinct points, which determine an element of `PSL(2, ℂ)`
continuously (`OnePoint.pslHomeomorphDistinctTriples`). -/
private theorem exists_continuous_leftInverse_rulingLeafPair (p₀ : OnePoint ℂ) :
    ∃ F : rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
        (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀ →
        PSL(2, ℂ) × PSL(2, ℂ),
      Continuous F ∧ ∀ g, F ⟨rulingLeafPair p₀ g, rulingLeafPair_mem_rulingIncidence p₀ g⟩ = g := by
  set t := (OnePoint.zeroOneInftyTriple ℂ : Fin 3 → OnePoint ℂ)
  -- On an incident pair `rulingLeafPair p₀ g`, the two triples of values are `g₁ • t` and
  -- `g₂ • t`, which consist of distinct points.
  have hinj (e : rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ
      (OnePoint ℂ)).prod (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀) :
      Injective (fun i ↦ (e.val.1 (t i)).1) ∧ Injective (fun i ↦ (e.val.2 (t i)).2) := by
    obtain ⟨g, hg⟩ := (rulingIncidence_prod_eq_range p₀).le e.property
    rw [← hg]
    exact ⟨(MulAction.injective g.1).comp (OnePoint.zeroOneInftyTriple ℂ).property,
      (MulAction.injective g.2).comp (OnePoint.zeroOneInftyTriple ℂ).property⟩
  let T := (OnePoint.pslHomeomorphDistinctTriples
    ⟨t, OnePoint.mem_distinctTriples.2 (OnePoint.zeroOneInftyTriple ℂ).property⟩).symm
  refine ⟨fun e ↦ (T ⟨_, OnePoint.mem_distinctTriples.2 (hinj e).1⟩,
    T ⟨_, OnePoint.mem_distinctTriples.2 (hinj e).2⟩), ?_, fun g ↦ ?_⟩
  · refine (T.continuous.comp (Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _)).prodMk
      (T.continuous.comp (Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _))
    · exact continuous_fst.comp ((continuous_eval_const (t i)).comp
        (continuous_fst.comp continuous_subtypeVal))
    · exact continuous_snd.comp ((continuous_eval_const (t i)).comp
        (continuous_snd.comp continuous_subtypeVal))
  · exact Prod.ext ((OnePoint.pslHomeomorphDistinctTriples_symm_eq_iff _ _ _).2 fun _ ↦ rfl)
      ((OnePoint.pslHomeomorphDistinctTriples_symm_eq_iff _ _ _).2 fun _ ↦ rfl)

/-- **The fibre of the incidence space for the product structure is `PSL(2, ℂ) × PSL(2, ℂ)`.** For
the product `J₀ = i × i`, the map `(a, b) ↦ (z ↦ (a • z, b • p₀), w ↦ (a • p₀, b • w))` is a
homeomorphism from `PSL(2, ℂ) × PSL(2, ℂ)` onto the incident pairs of ruling spheres, with the
compact-open topology on spheres. Its inverse is continuous because `a` and `b` depend continuously
on the values of the two spheres at `0`, `1` and `∞`. -/
def pslProdHomeomorphRulingIncidence (p₀ : OnePoint ℂ) :
    PSL(2, ℂ) × PSL(2, ℂ) ≃ₜ
      rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
        (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀ where
  toFun g := ⟨rulingLeafPair p₀ g, rulingLeafPair_mem_rulingIncidence p₀ g⟩
  invFun := (exists_continuous_leftInverse_rulingLeafPair p₀).choose
  left_inv := (exists_continuous_leftInverse_rulingLeafPair p₀).choose_spec.2
  right_inv := by
    rintro ⟨e, he⟩
    obtain ⟨g, rfl⟩ := (rulingIncidence_prod_eq_range p₀).le he
    exact congrArg (fun g ↦ (⟨rulingLeafPair p₀ g, rulingLeafPair_mem_rulingIncidence p₀ g⟩ :
      rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
        (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀))
      ((exists_continuous_leftInverse_rulingLeafPair p₀).choose_spec.2 g)
  continuous_toFun := (continuous_rulingLeafPair p₀).subtype_mk _
  continuous_invFun := (exists_continuous_leftInverse_rulingLeafPair p₀).choose_spec.1

@[simp]
theorem coe_pslProdHomeomorphRulingIncidence_apply (p₀ : OnePoint ℂ) (g : PSL(2, ℂ) × PSL(2, ℂ)) :
    (pslProdHomeomorphRulingIncidence p₀ g : C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ) ×
      C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ)) = rulingLeafPair p₀ g :=
  (rfl)

/-- The inverse of `TauCeti.pslProdHomeomorphRulingIncidence p₀` sends an incident pair `e` to the
unique `g` with `rulingLeafPair p₀ g = e`. -/
@[simp]
theorem rulingLeafPair_pslProdHomeomorphRulingIncidence_symm_apply (p₀ : OnePoint ℂ)
    (e : rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀) :
    rulingLeafPair p₀ ((pslProdHomeomorphRulingIncidence p₀).symm e) = e :=
  congrArg Subtype.val ((pslProdHomeomorphRulingIncidence p₀).apply_symm_apply e)

/-- **The fibre of the incidence space for the product structure is homotopy equivalent to
`SO(3) × SO(3)`**, since `PSL(2, ℂ)` deformation retracts onto its rotation subgroup
`PSU(2) ≅ SO(3)`. -/
def rulingIncidenceHomotopyEquiv (p₀ : OnePoint ℂ) :
    rulingIncidence ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
        (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) p₀ ≃ₕ
      specialOrthogonalGroup (Fin 3) ℝ × specialOrthogonalGroup (Fin 3) ℝ :=
  (pslProdHomeomorphRulingIncidence p₀).symm.toHomotopyEquiv.trans
    (pslHomotopyEquivSO3.prodCongr pslHomotopyEquivSO3)

/-- The homotopy inverse of `TauCeti.rulingIncidenceHomotopyEquiv p₀` sends a pair of rotations
`(R, S)` to the pair of leaves parametrized by the corresponding rotations of the Riemann sphere,
the elements of `PSU(2) ⊆ PSL(2, ℂ)` lifting `R` and `S`. -/
@[simp]
theorem coe_rulingIncidenceHomotopyEquiv_symm_apply (p₀ : OnePoint ℂ)
    (R S : specialOrthogonalGroup (Fin 3) ℝ) :
    ((rulingIncidenceHomotopyEquiv p₀).symm (R, S) : C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ) ×
        C(OnePoint ℂ, OnePoint ℂ × OnePoint ℂ)) =
      rulingLeafPair p₀ ((SU2.psuEquivSO3.symm R : PSL(2, ℂ)),
        (SU2.psuEquivSO3.symm S : PSL(2, ℂ))) := by
  -- The homotopy inverse of a product of homotopy equivalences is the product of their inverses.
  have h : (pslHomotopyEquivSO3.prodCongr pslHomotopyEquivSO3).symm.toFun (R, S) =
      (pslHomotopyEquivSO3.symm R, pslHomotopyEquivSO3.symm S) :=
    (rfl)
  simp [rulingIncidenceHomotopyEquiv, h]

end TauCeti
