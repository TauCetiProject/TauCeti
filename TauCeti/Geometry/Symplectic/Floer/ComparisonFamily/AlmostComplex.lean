/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ComparisonFamily
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
public import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.UnitInterval

/-!
# Almost complex structures along the cutoff and neck-stretching family

The comparison between the pair-of-pants product and the quantum product deforms a
pseudoholomorphic problem on a sphere, for a domain-independent compatible structure `J₀`, into
broken Floer configurations. Its Hamiltonian perturbations are the family
`K_R = ρ(R) K ∘ (σ_{L(R)} × id)` of `TauCeti.Floer.cutoffNeckFamily`, which switches `K` on for
`0 ≤ R ≤ 1` and inserts a neck of length `L(R)` at the line `s = c` for `R ≥ 1`. This file
constructs the matching family of domain-dependent almost complex structures.

Let `J(z, x)` be a family of `ω`-tame structures depending on a domain point `z = (s, t)` and an
external point `x` (a target point, say). The Cayley chart at `J₀` identifies the tame structures
with a convex ball of `J₀`-antilinear endomorphisms, with `J₀` at `0`. The ball is balanced
(`TauCeti.SymplecticForm.Tames.balanced_cayleyBall`), so scaling a Cayley coordinate by
`b ∈ [-1, 1]` stays in it. The family `TauCeti.Floer.cutoffNeckAlmostComplex` is

`J_R(z, x) = cayley⁻¹ (ρ(R) • cayley (J (σ_{L(R)}(s), t, x)))`,

with `ρ(R)` clamped to `[-1, 1]`. Thus `J_R` is the same Cayley rescaling `ρ(R)` as `K_R`,
applied to the structure with the same neck inserted. It has the following properties.

* Every `J_R(z, x)` is `ω`-tame, and `ω`-compatible when `J` is.
* At `ρ(R) = 0` it is the domain-independent structure `J₀`. At `ρ(R) = 1` it is `J` with a neck of
  length `L(R)` inserted, which is `J` itself where `L(R) = 0`.
* Along the neck `c ≤ s ≤ c + L(R)` it does not depend on `s`.
* Let `ρ` and `L ≥ 0` be smooth, and let `J` be smooth and independent of `s` near the line
  `s = c`. Then the family is smooth jointly in `R`, the domain point and the external point near
  every `R` with `|ρ| ≤ 1` nearby.
* If the values of `J` lie in a compact set of tame structures, then one pair of constants
  `a > 0` and `M` gives `a ‖v‖² ≤ ω(v, J_R(z, x) v)` and `‖J_R(z, x) v‖ ≤ M ‖v‖` for every member
  of the family, whatever the cutoff and however long the neck. Consequently the Floer energy
  density bounds the perturbed derivative of a solution uniformly over the family.

For the chosen cutoff `TauCeti.Floer.comparisonCutoff` and neck length
`TauCeti.Floer.comparisonNeckLength`, the family is `J₀` at `R = 0` and `J` on the collar
`2/3 ≤ R ≤ 3/2`, and it has a neck of length `R - 1` for `R ≥ 2`. If `J` is smooth and
independent of `s` near the line `s = c`, the family is smooth near every `R > -1`, in particular
across the endpoint `R = 0`.

As in `TauCeti.Geometry.Symplectic.Floer.ComparisonFamily`, the domain is a coordinate rectangle
with one neck and the structures act on a fixed symplectic vector space. The family on a sphere
with three necks and on the tangent bundle of a manifold is not treated here.

## Main definitions

* `TauCeti.Floer.cutoffNeckAlmostComplex h₀ J hJ ρ L c R`: the structure `J_R`.

## Main results

* `TauCeti.Floer.tames_cutoffNeckAlmostComplex` and
  `TauCeti.Floer.compatible_cutoffNeckAlmostComplex`: tameness and compatibility.
* `TauCeti.Floer.cayley_cutoffNeckAlmostComplex_of_abs_le`: the Cayley coordinate of `J_R` is
  `ρ(R)` times that of the stretched structure.
* `TauCeti.Floer.cutoffNeckAlmostComplex_of_cutoff_eq_zero`,
  `TauCeti.Floer.cutoffNeckAlmostComplex_of_cutoff_eq_one`: the two ends of the cutoff.
* `TauCeti.Floer.contDiffAt_cutoffNeckAlmostComplex`: smoothness of the family.
* `TauCeti.Floer.exists_pos_forall_mul_norm_sq_le_cutoffNeckAlmostComplex`: uniform tameness and
  boundedness constants.
* `TauCeti.Floer.exists_pos_forall_mul_norm_sq_le_floerEnergyDensity_cutoffNeckAlmostComplex`:
  the uniform energy coercivity for solutions of the Floer equation.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Section 2.5,
  on the Cayley chart of the tame and compatible structures.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures for inhomogeneous equations.
-/

public noncomputable section

open Filter Function Set Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

section Family

variable {X : Type*} {J : ℝ × ℝ → X → AlmostComplexStructure V} {hJ : ∀ z x, ω.Tames (J z x)}
  {ρ L : ℝ → ℝ} {c R : ℝ}

/-- The almost complex structures of the cutoff and neck-stretching family, relative to an
`ω`-compatible structure `J₀`. At the parameter `R`, the domain point `z = (s, t)` and the point
`x`, it is the tame structure whose Cayley coordinate at `J₀` is `ρ(R)`, clamped to `[-1, 1]` by
`Set.projIcc`, times the Cayley coordinate of `J(σ(s), t, x)`. Here `σ = neckCollapse c (L R)`
inserts a neck of length `L(R)` at the line `s = c`. -/
def cutoffNeckAlmostComplex (h₀ : ω.Compatible J₀) (J : ℝ × ℝ → X → AlmostComplexStructure V)
    (hJ : ∀ z x, ω.Tames (J z x)) (ρ L : ℝ → ℝ) (c R : ℝ) (z : ℝ × ℝ) (x : X) :
    AlmostComplexStructure V :=
  h₀.cayleyEquiv.symm
    ⟨(projIcc (-1) 1 (by norm_num) (ρ R) : ℝ) •
        J₀.cayley (J (neckCollapse c (L R) z.1, z.2) x),
      h₀.smul_cayley_mem_cayleyBall (hJ _ _) (abs_projIcc_le _ _)⟩

/-- Every member of the family is tamed by `ω`. -/
theorem tames_cutoffNeckAlmostComplex (h₀ : ω.Compatible J₀) (R : ℝ) (z : ℝ × ℝ) (x : X) :
    ω.Tames (cutoffNeckAlmostComplex h₀ J hJ ρ L c R z x) :=
  (h₀.cayleyEquiv.symm _).2

/-- The Cayley coordinate of a member of the family is the clamped cutoff times the Cayley
coordinate of the stretched structure. This characterizes the member, since the Cayley transform
is injective on tame structures. -/
theorem cayley_cutoffNeckAlmostComplex (h₀ : ω.Compatible J₀) (R : ℝ) (z : ℝ × ℝ) (x : X) :
    J₀.cayley (cutoffNeckAlmostComplex h₀ J hJ ρ L c R z x) =
      (projIcc (-1) 1 (by norm_num) (ρ R) : ℝ) •
        J₀.cayley (J (neckCollapse c (L R) z.1, z.2) x) := by
  rw [cutoffNeckAlmostComplex, ← h₀.cayleyEquiv_apply_coe, Equiv.apply_symm_apply]

/-- Where `|ρ(R)| ≤ 1`, the Cayley coordinate of a member of the family is `ρ(R)` times the Cayley
coordinate of the stretched structure. -/
@[simp]
theorem cayley_cutoffNeckAlmostComplex_of_abs_le (h₀ : ω.Compatible J₀) (hρ : |ρ R| ≤ 1)
    (z : ℝ × ℝ) (x : X) :
    J₀.cayley (cutoffNeckAlmostComplex h₀ J hJ ρ L c R z x) =
      ρ R • J₀.cayley (J (neckCollapse c (L R) z.1, z.2) x) := by
  rw [cayley_cutoffNeckAlmostComplex, projIcc_of_mem _ (abs_le.1 hρ)]

/-- The family is `ω`-compatible when `J` is. -/
theorem compatible_cutoffNeckAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ z x, ω.Compatible (J z x)) (R : ℝ) (z : ℝ × ℝ) (x : X) :
    ω.Compatible (cutoffNeckAlmostComplex h₀ J hJ ρ L c R z x) := by
  refine (h₀.cayley_mem_compatibleCayleyBall_iff (tames_cutoffNeckAlmostComplex h₀ R z x)).mp ?_
  rw [cayley_cutoffNeckAlmostComplex]
  exact h₀.smul_cayley_mem_compatibleCayleyBall (hJc _ _)
    (abs_projIcc_le _ _)

/-- Where the cutoff vanishes, the family is the domain-independent structure `J₀`. -/
theorem cutoffNeckAlmostComplex_of_cutoff_eq_zero (h₀ : ω.Compatible J₀) (h : ρ R = 0) :
    cutoffNeckAlmostComplex h₀ J hJ ρ L c R = fun _ _ ↦ J₀ := by
  funext z x
  refine h₀.eq_of_cayley_eq (tames_cutoffNeckAlmostComplex h₀ R z x) h₀.tames ?_
  rw [cayley_cutoffNeckAlmostComplex_of_abs_le h₀ (by simp [h]), h, zero_smul,
    AlmostComplexStructure.cayley_self]

/-- Where the cutoff is `1`, the family is `J` with a neck of length `L(R)` inserted. -/
theorem cutoffNeckAlmostComplex_of_cutoff_eq_one (h₀ : ω.Compatible J₀) (h : ρ R = 1) :
    cutoffNeckAlmostComplex h₀ J hJ ρ L c R = neckStretch c (L R) J := by
  funext z x
  refine h₀.eq_of_cayley_eq (tames_cutoffNeckAlmostComplex h₀ R z x) ?_ ?_
  · rw [neckStretch_apply]
    exact hJ _ _
  · rw [cayley_cutoffNeckAlmostComplex_of_abs_le h₀ (by simp [h]), h, one_smul, neckStretch_apply]

/-- Along the neck `c ≤ s ≤ c + L(R)` the family does not depend on `s`. -/
theorem cutoffNeckAlmostComplex_apply_eq_of_mem_Icc (h₀ : ω.Compatible J₀) (hL : 0 ≤ L R)
    {s : ℝ} (hs : s ∈ Icc c (c + L R)) (t : ℝ) (x : X) :
    cutoffNeckAlmostComplex h₀ J hJ ρ L c R (s, t) x =
      cutoffNeckAlmostComplex h₀ J hJ ρ L c R (c, t) x := by
  refine h₀.eq_of_cayley_eq (tames_cutoffNeckAlmostComplex h₀ R _ x)
    (tames_cutoffNeckAlmostComplex h₀ R _ x) ?_
  simp only [cayley_cutoffNeckAlmostComplex, neckCollapse_of_mem_Icc hs,
    neckCollapse_of_le hL le_rfl]

/-- In operator-norm coordinates, a member of the family is the Cayley path expression
`J₀ (1 + b C)(1 - b C)⁻¹`, where `b` is the clamped cutoff and `C` is the Cayley coordinate of the
stretched structure. -/
theorem toContinuousLinearMap_cutoffNeckAlmostComplex (h₀ : ω.Compatible J₀) (R : ℝ)
    (z : ℝ × ℝ) (x : X) :
    LinearMap.toContinuousLinearMap (cutoffNeckAlmostComplex h₀ J hJ ρ L c R z x).toLinearMap =
      cayleyPathFormula (projIcc (-1) 1 (by norm_num) (ρ R) : ℝ)
        (LinearMap.toContinuousLinearMap J₀.toLinearMap)
        (LinearMap.toContinuousLinearMap (J (neckCollapse c (L R) z.1, z.2) x).toLinearMap) :=
  h₀.toContinuousLinearMap_cayleyEquiv_symm_smul_cayley (hJ _ _)
    (abs_projIcc_le _ _) (LinearMap.coe_toContinuousLinearMap _)
    (LinearMap.coe_toContinuousLinearMap _)

/-- For the chosen cutoff and neck length, the family starts at the domain-independent structure
`J₀`. -/
@[simp]
theorem cutoffNeckAlmostComplex_comparison_zero (h₀ : ω.Compatible J₀) :
    cutoffNeckAlmostComplex h₀ J hJ comparisonCutoff comparisonNeckLength c 0 = fun _ _ ↦ J₀ :=
  cutoffNeckAlmostComplex_of_cutoff_eq_zero h₀ comparisonCutoff_zero

/-- For the chosen cutoff and neck length, the family is constant, equal to `J`, on the collar
`2/3 ≤ R ≤ 3/2` joining the cutoff phase to the neck-stretching phase. -/
theorem cutoffNeckAlmostComplex_comparison_of_mem_Icc (h₀ : ω.Compatible J₀)
    (hR : R ∈ Icc (2 / 3 : ℝ) (3 / 2)) :
    cutoffNeckAlmostComplex h₀ J hJ comparisonCutoff comparisonNeckLength c R = J := by
  rw [cutoffNeckAlmostComplex_of_cutoff_eq_one h₀ (comparisonCutoff_of_ge hR.1),
    comparisonNeckLength_of_le hR.2, neckStretch_zero]

/-- For the chosen cutoff and neck length, for `R ≥ 2` the family is `J` with a neck of length
`R - 1`. -/
theorem cutoffNeckAlmostComplex_comparison_of_two_le (h₀ : ω.Compatible J₀) (hR : 2 ≤ R) :
    cutoffNeckAlmostComplex h₀ J hJ comparisonCutoff comparisonNeckLength c R =
      neckStretch c (R - 1) J := by
  rw [cutoffNeckAlmostComplex_of_cutoff_eq_one h₀ (comparisonCutoff_of_ge (by linarith)),
    comparisonNeckLength_of_ge hR]

end Family

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {J : ℝ × ℝ → E → AlmostComplexStructure V} {hJ : ∀ z x, ω.Tames (J z x)}
  {ρ L : ℝ → ℝ} {c R : ℝ}

/-- **Smoothness of the family.** Let `ρ` and `L ≥ 0` be smooth, and let `J` be a smooth family of
tame structures which is independent of `s` near the line `s = c`. Near every `R` around which
`|ρ| ≤ 1`, the family is smooth jointly in the parameter, the domain point and the external
point. -/
theorem contDiffAt_cutoffNeckAlmostComplex (h₀ : ω.Compatible J₀) {n : WithTop ℕ∞}
    (hρ : ContDiff ℝ n ρ) (hρR : ∀ᶠ R' in 𝓝 R, |ρ R'| ≤ 1) (hL : ContDiff ℝ n L)
    (hL₀ : ∀ R, 0 ≤ L R) (hJc : ∀ᶠ s in 𝓝 c, ∀ t, J (s, t) = J (c, t))
    (hJd : ContDiff ℝ n fun p : (ℝ × ℝ) × E ↦
      LinearMap.toContinuousLinearMap (J p.1 p.2).toLinearMap)
    (z : ℝ × ℝ) (x : E) :
    ContDiffAt ℝ n (fun q : ℝ × (ℝ × ℝ) × E ↦ LinearMap.toContinuousLinearMap
      (cutoffNeckAlmostComplex h₀ J hJ ρ L c q.1 q.2.1 q.2.2).toLinearMap) (R, z, x) := by
  set A := LinearMap.toContinuousLinearMap J₀.toLinearMap
  set G : ℝ × ℝ → E → V →L[ℝ] V := fun w y ↦ LinearMap.toContinuousLinearMap (J w y).toLinearMap
  have hGc : ∀ᶠ s in 𝓝 c, ∀ t, G (s, t) = G (c, t) :=
    hJc.mono fun s hs t ↦ by simp only [G, hs t]
  -- The operators of the stretched structure are smooth, by the smoothness of neck insertion.
  have hN := contDiff_neckStretch_family hL hL₀ hGc hJd
  -- At the base point both denominators of the Cayley path expression are invertible.
  have hB : (G (neckCollapse c (L R) z.1, z.2) x).toLinearMap =
      (J (neckCollapse c (L R) z.1, z.2) x).toLinearMap :=
    LinearMap.coe_toContinuousLinearMap _
  have hA : A.toLinearMap = J₀.toLinearMap := LinearMap.coe_toContinuousLinearMap _
  have hcf := contDiffAt_cayleyPathFormula (n := n)
    (h₀.tames.isUnit_one_sub_mul_of_toLinearMap (hJ _ _) hA hB)
    (h₀.isUnit_one_sub_smul_cayleyFormula (hJ _ _) hρR.self_of_nhds hA hB)
  have hin : ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) × E ↦
      (ρ q.1, A, neckStretch c (L q.1) G q.2.1 q.2.2) :=
    (hρ.comp contDiff_fst).prodMk (contDiff_const.prodMk hN)
  -- Write the base point of `hcf` as the value of `hin` at `(R, z, x)`.
  rw [← neckStretch_apply (K := G)] at hcf
  refine (hcf.comp (R, z, x) hin.contDiffAt).congr_of_eventuallyEq ?_
  -- Near the base point the clamped cutoff is the cutoff itself.
  filter_upwards [(continuous_fst.tendsto (R, z, x)).eventually hρR] with q hq
  rw [toContinuousLinearMap_cutoffNeckAlmostComplex, projIcc_of_mem _ (abs_le.1 hq)]
  simp only [comp_apply, neckStretch_apply, G, A]

/-- For the chosen cutoff and neck length, and `J` smooth and independent of `s` near the line
`s = c`, the family is smooth near every `R > -1`, in particular across the endpoint `R = 0` of
the comparison family. -/
theorem contDiffAt_cutoffNeckAlmostComplex_comparison (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hR : -1 < R) (hJc : ∀ᶠ s in 𝓝 c, ∀ t, J (s, t) = J (c, t))
    (hJd : ContDiff ℝ n fun p : (ℝ × ℝ) × E ↦
      LinearMap.toContinuousLinearMap (J p.1 p.2).toLinearMap)
    (z : ℝ × ℝ) (x : E) :
    ContDiffAt ℝ n (fun q : ℝ × (ℝ × ℝ) × E ↦ LinearMap.toContinuousLinearMap
      (cutoffNeckAlmostComplex h₀ J hJ comparisonCutoff comparisonNeckLength c q.1 q.2.1
        q.2.2).toLinearMap) (R, z, x) :=
  contDiffAt_cutoffNeckAlmostComplex h₀ contDiff_comparisonCutoff
    (Filter.mem_of_superset (Ioi_mem_nhds hR) fun _ h ↦ abs_comparisonCutoff_le_one (le_of_lt h))
    contDiff_comparisonNeckLength comparisonNeckLength_nonneg hJc hJd z x

end Smooth

section Uniform

variable {X : Type*} {J : ℝ × ℝ → X → AlmostComplexStructure V}

/-- **Uniform tameness over the family.** If the values of `J` lie in a compact set of `ω`-tame
structures, then there are constants `a > 0` and `M` with `a ‖v‖² ≤ ω(v, J_R(z, x) v)` and
`‖J_R(z, x) v‖ ≤ M ‖v‖` for every member `J_R(z, x)` of the family and every vector `v`. The
constants do not depend on the cutoff, the neck length or the neck position. -/
theorem exists_pos_forall_mul_norm_sq_le_cutoffNeckAlmostComplex (h₀ : ω.Compatible J₀)
    {𝒦 : Set (AlmostComplexStructure V)} (h𝒦 : IsCompact 𝒦) (h𝒦t : ∀ J' ∈ 𝒦, ω.Tames J')
    (hJ𝒦 : ∀ z x, J z x ∈ 𝒦) :
    ∃ a > 0, ∃ M, ∀ (ρ L : ℝ → ℝ) (c R : ℝ) (z : ℝ × ℝ) (x : X) (v : V),
      a * ‖v‖ ^ 2 ≤
          ω v (cutoffNeckAlmostComplex h₀ J (fun z x ↦ h𝒦t _ (hJ𝒦 z x)) ρ L c R z x v) ∧
        ‖cutoffNeckAlmostComplex h₀ J (fun z x ↦ h𝒦t _ (hJ𝒦 z x)) ρ L c R z x v‖ ≤
          M * ‖v‖ := by
  set A := LinearMap.toContinuousLinearMap J₀.toLinearMap
  set e : AlmostComplexStructure V → V →L[ℝ] V := fun J' ↦
    LinearMap.toContinuousLinearMap J'.toLinearMap
  have hA : A.toLinearMap = J₀.toLinearMap := LinearMap.coe_toContinuousLinearMap _
  -- The operators of all members lie in the compact set `T` of Cayley path expressions.
  set T := (fun p : ℝ × (V →L[ℝ] V) ↦ cayleyPathFormula p.1 A p.2) '' (Icc (-1) 1 ×ˢ (e '' 𝒦))
  have hT : IsCompact T := h₀.isCompact_image_cayleyPathFormula hA h𝒦 h𝒦t
  -- Each element of `T` is the operator of a tame structure, so `ω` is uniformly positive on `T`.
  obtain ⟨a, ha, hle⟩ := hT.exists_pos_forall_mul_norm_sq_le_compRight
    ω.toBilinForm.toContinuousBilinearMap (by
      rintro _ ⟨⟨b, _⟩, ⟨hb, J', hJ', rfl⟩, rfl⟩ v hv
      dsimp only
      rw [← h₀.toContinuousLinearMap_cayleyEquiv_symm_smul_cayley (h𝒦t J' hJ') (abs_le.2 hb) hA
        (LinearMap.coe_toContinuousLinearMap _)]
      exact (h₀.cayleyEquiv.symm _).2 v hv)
  obtain ⟨M, hM⟩ := hT.isBounded.exists_norm_le
  refine ⟨a, ha, M, fun ρ L c R z x v ↦ ?_⟩
  set F := cutoffNeckAlmostComplex h₀ J (fun z x ↦ h𝒦t _ (hJ𝒦 z x)) ρ L c R z x
  have hmem : e F ∈ T :=
    ⟨((projIcc (-1) 1 (by norm_num) (ρ R) : ℝ), e (J (neckCollapse c (L R) z.1, z.2) x)),
      ⟨(projIcc (-1) 1 (by norm_num) (ρ R)).2, mem_image_of_mem e (hJ𝒦 _ _)⟩,
      (toContinuousLinearMap_cutoffNeckAlmostComplex h₀ R z x).symm⟩
  have hFv : e F v = F v := by simp [e]
  refine ⟨hle _ hmem v, ?_⟩
  rw [← hFv]
  exact (e F).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hM _ hmem) (norm_nonneg v))

/-- **Uniform energy coercivity over the family.** If the values of `J` lie in a compact set of
`ω`-tame structures, there are constants `a > 0` and `C` such that, for every member of the
family, every perturbation `K = K_s ds + K_t dt` and every map `u` solving the Floer equation at
`z` for the structure `J_R(z, u z)`, the Floer energy density at `z` controls the perturbed
derivative: `a (‖∂_s u - X_{K_s}‖² + ‖∂_t u - X_{K_t}‖²) ≤ C ω(∂_s u - X_{K_s}, ∂_t u - X_{K_t})`.
The constants do not depend on the cutoff, the neck length or the neck position. -/
theorem exists_pos_forall_mul_norm_sq_le_floerEnergyDensity_cutoffNeckAlmostComplex
    (h₀ : ω.Compatible J₀) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {𝒦 : Set (AlmostComplexStructure V)} (h𝒦 : IsCompact 𝒦) (h𝒦t : ∀ J' ∈ 𝒦, ω.Tames J')
    (hJ𝒦 : ∀ z x, J z x ∈ 𝒦) :
    ∃ a > 0, ∃ C, ∀ (ρ L : ℝ → ℝ) (c R : ℝ) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
      (z : ℝ × ℝ),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          (cutoffNeckAlmostComplex h₀ J (fun z x ↦ h𝒦t _ (hJ𝒦 z x)) ρ L c R z (u z))
          (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V) →
        a * (‖ω.perturbedFDeriv Ks Kt u z stdComplexLineReal‖ ^ 2 +
            ‖ω.perturbedFDeriv Ks Kt u z stdComplexLineImag‖ ^ 2) ≤
          C * ω.floerEnergyDensity Ks Kt u z := by
  obtain ⟨a, ha, M, h⟩ := exists_pos_forall_mul_norm_sq_le_cutoffNeckAlmostComplex h₀ h𝒦 h𝒦t hJ𝒦
  exact ⟨a, ha, 1 + M ^ 2, fun ρ L c R Ks Kt u z hu ↦
    ω.mul_norm_sq_add_norm_sq_perturbedFDeriv_le_mul_floerEnergyDensity ha.le
      (fun v ↦ (h ρ L c R z (u z) v).1) (fun v ↦ (h ρ L c R z (u z) v).2) hu⟩

end Uniform

end TauCeti.Floer
