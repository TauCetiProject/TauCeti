/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InvariantForm.Basic
public import TauCeti.Analysis.PDE.YangMills.SelfDuality
public import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# The curvature term of the Weitzenböck formula and the cubic bound

Let `E` be a finite-dimensional real inner product space and `V` a real Lie algebra, for
Yang–Mills theory the Lie algebra `𝔤` of the structure group. As in
`TauCeti.Analysis.InnerProductSpace.HodgeStar.VectorValued`, a `V`-valued two-form is a linear map
`F : ⋀² E →ₗ[ℝ] V`, with coefficients `F_ij = F (eᵢ ∧ eⱼ)` in an orthonormal frame `(eᵢ)`. The
curvature term of the Weitzenböck formula for `V`-valued two-forms is the bilinear operation

`𝔉_F(ω)_ij = ∑ₗ (⁅F_il, ω_lj⁆ - ⁅F_jl, ω_li⁆)`

(`TauCeti.weitzenbockCurvatureTerm`), defined without a frame through the metric trace. Reading
two-forms as skew-symmetric matrices with entries in `V`, it is `F ⬝ ω + ω ⬝ F`, where the
products of entries in the matrix products are Lie brackets. Equivalently, for
`F = ∑ₐ Aₐ ⊗ Xₐ` and `ω = ∑_b B_b ⊗ Y_b` with scalar skew-symmetric matrices `Aₐ`, `B_b` and
`Xₐ`, `Y_b` in `V`, it is `∑ₐ ∑_b [Aₐ, B_b] ⊗ ⁅Xₐ, Y_b⁆`, built from the commutators of the
scalar matrices. For the curvature `F` of a harmonic Yang–Mills connection on `ℝ⁴` it is the
zeroth-order term of the Weitzenböck formula
`½ Δ|F⁺|² = |∇F⁺|² - ⟨F⁺, 𝔉_{F⁺}(F⁺)⟩`, and the cubic bound below, which controls it by the norm
`γ₀` of the Lie bracket (`QuadraticMap.lieBracketNorm`), is the pointwise input of the energy gap
for harmonic Yang–Mills connections.

In dimension four, self-dual and anti-self-dual two-forms commute as skew-symmetric matrices, so
`𝔉_F(ω) = 0` for anti-self-dual `F` and self-dual `ω`, and hence `𝔉_F(ω) = 𝔉_{F⁺}(ω)` for every
`F` when `ω` is self-dual. For a self-dual `ω`, a positively oriented orthonormal frame and a
symmetric `ad`-invariant form `B` on `V`,

`⟨ω, 𝔉_ω(ω)⟩ = -24 B (ω₀₁, ⁅ω₀₂, ω₀₃⁆)`.

In the orthonormal basis `(e⁰ ∧ e¹ + e² ∧ e³) / √2`, `(e⁰ ∧ e² - e¹ ∧ e³) / √2`,
`(e⁰ ∧ e³ + e¹ ∧ e²) / √2` of the self-dual two-forms, whose coefficients are
`ωᵃ = √2 ω₀ₐ`, this reads `⟨ω, 𝔉_ω(ω)⟩ = -6√2 ⟨ω¹, ⁅ω², ω³⁆⟩`. Together with
`|⁅X, Y⁆| ≤ γ₀ |X| |Y|`, Cauchy–Schwarz and the arithmetic–geometric mean inequality this gives the
**cubic bound** `|⟨ω, 𝔉_ω(ω)⟩| ≤ (2√6/3) γ₀ |ω|³`, where `|ω|² = ⟨ω, ω⟩ = ∑_{i < j} |ω_ij|²`.

## Main definitions

* `TauCeti.weitzenbockCurvatureTerm`: the bilinear map `(F, ω) ↦ 𝔉_F(ω)`.

## Main results

* `TauCeti.weitzenbockCurvatureTerm_apply_ιMulti`: `𝔉_F(ω)` in an orthonormal basis.
* `TauCeti.weitzenbockCurvatureTerm_comm`: the curvature term is symmetric, `𝔉_F(ω) = 𝔉_ω(F)`.
* `TauCeti.weitzenbockCurvatureTerm_eq_zero_of_vectorFormHodgeStar_eq_neg`: `𝔉_F(ω) = 0` for
  anti-self-dual `F` and self-dual `ω`, and
  `TauCeti.weitzenbockCurvatureTerm_vectorFormSelfDualPart`: `𝔉_{F⁺}(ω) = 𝔉_F(ω)` for self-dual
  `ω`.
* `TauCeti.vectorFormInner_weitzenbockCurvatureTerm_of_vectorFormHodgeStar_eq_self`:
  `⟨ω, 𝔉_ω(ω)⟩ = -24 B (ω₀₁, ⁅ω₀₂, ω₀₃⁆)` for self-dual `ω`.
* `TauCeti.abs_vectorFormInner_weitzenbockCurvatureTerm_le`: the cubic bound
  `|⟨ω, 𝔉_ω(ω)⟩| ≤ (2√6/3) γ₀ |ω|³` for self-dual `ω`, and
  `TauCeti.CompactMatrixStructureGroup.abs_vectorFormInner_weitzenbockCurvatureTerm_le` for the Lie
  algebra of a compact matrix structure group.

## References

* S. Gursky, C. Kelleher and J. Streets, *A conformally invariant gap theorem in Yang–Mills
  theory*, Comm. Math. Phys. 361 (2018), arXiv:1708.01157, Definition 2.3 and Lemma 2.6.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Lemma 6.4.
-/

public section

noncomputable section

open Module exteriorPower
open LinearMap (BilinMap)
open scoped RealInnerProductSpace

variable {E V W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [LieRing V] [LieAlgebra ℝ V] [LieRing W] [LieAlgebra ℝ W]

namespace TauCeti

/-- The wedge `u ∧ v` of two vectors as a bilinear map. -/
private abbrev wedgeTwo : E →ₗ[ℝ] E →ₗ[ℝ] ⋀[ℝ]^2 E :=
  (ιMulti ℝ 2 : E [⋀^Fin 2]→ₗ[ℝ] ⋀[ℝ]^2 E).toMultilinearMap.toBilinMap

/-- The bilinear map `(u, v) ↦ ∑ₗ ⁅F (u ∧ bₗ), ω (bₗ ∧ v)⁆` for the standard orthonormal basis `b`;
it is the metric trace of `(a, c) ↦ ⁅F (u ∧ a), ω (c ∧ v)⁆`, so it does not depend on `b`
(`TauCeti.bracketTrace_apply`). -/
private def bracketTrace (F ω : ⋀[ℝ]^2 E →ₗ[ℝ] V) : E →ₗ[ℝ] E →ₗ[ℝ] V :=
  ∑ l, (LieAlgebra.ad ℝ V : V →ₗ[ℝ] Module.End ℝ V).compl₁₂
    (F ∘ₗ wedgeTwo.flip (stdOrthonormalBasis ℝ E l)) (ω ∘ₗ wedgeTwo (stdOrthonormalBasis ℝ E l))

/-- `bracketTrace F ω u v = ∑ₗ ⁅F (u ∧ eₗ), ω (eₗ ∧ v)⁆` for every orthonormal basis `e`. -/
private theorem bracketTrace_apply {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E)
    (F ω : ⋀[ℝ]^2 E →ₗ[ℝ] V) (u v : E) :
    bracketTrace F ω u v = ∑ l, ⁅F (ιMulti ℝ 2 ![u, e l]), ω (ιMulti ℝ 2 ![e l, v])⁆ := by
  let X := (LieAlgebra.ad ℝ V : V →ₗ[ℝ] Module.End ℝ V).compl₁₂ (F ∘ₗ wedgeTwo u)
    (ω ∘ₗ wedgeTwo.flip v)
  have h₁ := BilinMap.metricTrace_eq_sum X (stdOrthonormalBasis ℝ E)
  have h₂ := BilinMap.metricTrace_eq_sum X e
  simp only [X, LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.flip_apply,
    MultilinearMap.toBilinMap_apply, AlternatingMap.coe_multilinearMap, LieHom.coe_toLinearMap,
    LieAlgebra.ad_apply] at h₁ h₂
  rw [← h₂, h₁, bracketTrace]
  simp

private theorem isAlt_bracketTrace_sub_flip (F ω : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    (bracketTrace F ω - (bracketTrace F ω).flip).IsAlt := fun u ↦ by simp

/-- **The curvature term of the Weitzenböck formula** for `V`-valued two-forms, `V` a real Lie
algebra: for two-forms `F` and `ω`,
`𝔉_F(ω)(u ∧ v) = ∑ₗ (⁅F (u ∧ eₗ), ω (eₗ ∧ v)⁆ - ⁅F (v ∧ eₗ), ω (eₗ ∧ u)⁆)`
for any orthonormal basis `(eₗ)` (`TauCeti.weitzenbockCurvatureTerm_apply_ιMulti`). In
coefficients, `𝔉_F(ω)_ij = ∑ₗ (⁅F_il, ω_lj⁆ - ⁅F_jl, ω_li⁆)`. It is bilinear in `F` and `ω`. -/
def weitzenbockCurvatureTerm :
    (⋀[ℝ]^2 E →ₗ[ℝ] V) →ₗ[ℝ] (⋀[ℝ]^2 E →ₗ[ℝ] V) →ₗ[ℝ] ⋀[ℝ]^2 E →ₗ[ℝ] V :=
  LinearMap.mk₂ ℝ
    (fun F ω ↦ alternatingMapLinearEquiv (isAlt_bracketTrace_sub_flip F ω).toAlternatingMap)
    (fun F F' ω ↦ linearMap_ext_ιMulti_two fun u v ↦ by
      simp [alternatingMapLinearEquiv_apply_ιMulti, bracketTrace_apply (stdOrthonormalBasis ℝ E),
        Finset.sum_add_distrib]
      abel)
    (fun c F ω ↦ linearMap_ext_ιMulti_two fun u v ↦ by
      simp [alternatingMapLinearEquiv_apply_ιMulti, bracketTrace_apply (stdOrthonormalBasis ℝ E),
        Finset.smul_sum, smul_sub])
    (fun F ω ω' ↦ linearMap_ext_ιMulti_two fun u v ↦ by
      simp [alternatingMapLinearEquiv_apply_ιMulti, bracketTrace_apply (stdOrthonormalBasis ℝ E),
        Finset.sum_add_distrib]
      abel)
    (fun c F ω ↦ linearMap_ext_ιMulti_two fun u v ↦ by
      simp [alternatingMapLinearEquiv_apply_ιMulti, bracketTrace_apply (stdOrthonormalBasis ℝ E),
        Finset.smul_sum, smul_sub])

/-- **The curvature term in an orthonormal basis**:
`𝔉_F(ω)(u ∧ v) = ∑ₗ (⁅F (u ∧ eₗ), ω (eₗ ∧ v)⁆ - ⁅F (v ∧ eₗ), ω (eₗ ∧ u)⁆)`. -/
theorem weitzenbockCurvatureTerm_apply_ιMulti {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (F ω : ⋀[ℝ]^2 E →ₗ[ℝ] V) (u v : E) :
    weitzenbockCurvatureTerm F ω (ιMulti ℝ 2 ![u, v]) =
      ∑ l, (⁅F (ιMulti ℝ 2 ![u, e l]), ω (ιMulti ℝ 2 ![e l, v])⁆ -
        ⁅F (ιMulti ℝ 2 ![v, e l]), ω (ιMulti ℝ 2 ![e l, u])⁆) := by
  simp [weitzenbockCurvatureTerm, alternatingMapLinearEquiv_apply_ιMulti, bracketTrace_apply e]

/-- **The curvature term is symmetric**: `𝔉_F(ω) = 𝔉_ω(F)`. -/
theorem weitzenbockCurvatureTerm_comm (F ω : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    weitzenbockCurvatureTerm F ω = weitzenbockCurvatureTerm ω F :=
  linearMap_ext_ιMulti_two fun u v ↦ by
    simp only [weitzenbockCurvatureTerm_apply_ιMulti (stdOrthonormalBasis ℝ E)]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [ιMulti_two_swap v, ιMulti_two_swap u]
    simp only [map_neg, lie_neg]
    rw [← lie_skew (ω _), ← lie_skew (ω _)]
    abel

/-- For an abelian Lie algebra of values the curvature term vanishes. -/
@[simp]
theorem weitzenbockCurvatureTerm_eq_zero_of_isLieAbelian [IsLieAbelian V]
    (F ω : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    weitzenbockCurvatureTerm F ω = 0 :=
  linearMap_ext_ιMulti_two fun u v ↦ by
    simp [weitzenbockCurvatureTerm_apply_ιMulti (stdOrthonormalBasis ℝ E), trivial_lie_zero]

/-- The curvature term commutes with a Lie algebra homomorphism `f` of the values, such as
`Ad(g)`: `𝔉_{f ∘ F}(f ∘ ω) = f ∘ 𝔉_F(ω)`. -/
theorem weitzenbockCurvatureTerm_comp (f : V →ₗ⁅ℝ⁆ W) (F ω : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    weitzenbockCurvatureTerm ((f : V →ₗ[ℝ] W) ∘ₗ F) ((f : V →ₗ[ℝ] W) ∘ₗ ω) =
      (f : V →ₗ[ℝ] W) ∘ₗ weitzenbockCurvatureTerm F ω :=
  linearMap_ext_ιMulti_two fun u v ↦ by
    simp [weitzenbockCurvatureTerm_apply_ιMulti (stdOrthonormalBasis ℝ E)]

/-! ### Self-dual forms in dimension four -/

open LinearMap.BilinForm

section FourDimensional

variable [Fact (finrank ℝ E = 4)] {o : Orientation ℝ E (Fin 4)} (hkl : 2 + 2 = finrank ℝ E)

/-- **Self-dual and anti-self-dual forms commute**: in dimension four, `𝔉_F(ω) = 0` for an
anti-self-dual `F`, `⋆F = -F`, and a self-dual `ω`, `⋆ω = ω`. -/
theorem weitzenbockCurvatureTerm_eq_zero_of_vectorFormHodgeStar_eq_neg
    {F ω : ⋀[ℝ]^2 E →ₗ[ℝ] V} (hF : o.vectorFormHodgeStar hkl F = -F)
    (hω : o.vectorFormHodgeStar hkl ω = ω) : weitzenbockCurvatureTerm F ω = 0 := by
  let e := o.finOrthonormalBasis (by norm_num) (Fact.out : finrank ℝ E = 4)
  have he : e.toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
  obtain ⟨hF23, hF13, hF12⟩ := o.apply_ιMulti_two_of_vectorFormHodgeStar_eq_neg hkl he hF
  obtain ⟨hω23, hω13, hω12⟩ := o.apply_ιMulti_two_of_vectorFormHodgeStar_eq_self hkl he hω
  suffices h : wedgeTwo.compr₂ (weitzenbockCurvatureTerm F ω) = 0 from
    linearMap_ext_ιMulti_two fun u v ↦ by simpa using congr($h u v)
  refine LinearMap.ext_basis e.toBasis e.toBasis fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [weitzenbockCurvatureTerm_apply_ιMulti e, Fin.sum_univ_four,
      ιMulti_two_swap_of_lt e, hF23, hF13, hF12, hω23, hω13, hω12] <;> abel

/-- **The cubic term of a self-dual form in a positive frame**: for a positively oriented
orthonormal basis `e` in dimension four, a symmetric `ad`-invariant bilinear form `B` on `V` and a
self-dual `ω`, `⟨ω, 𝔉_ω(ω)⟩ = -24 B (ω₀₁, ⁅ω₀₂, ω₀₃⁆)`, where `ω_ij = ω (eᵢ ∧ eⱼ)`. -/
theorem vectorFormInner_weitzenbockCurvatureTerm_of_vectorFormHodgeStar_eq_self
    {e : OrthonormalBasis (Fin 4) ℝ E} (he : e.toBasis.orientation = o)
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (hinv : B.lieInvariant V)
    {ω : ⋀[ℝ]^2 E →ₗ[ℝ] V} (hω : o.vectorFormHodgeStar hkl ω = ω) :
    vectorFormInner B 2 ω (weitzenbockCurvatureTerm ω ω) =
      -24 * B (ω (ιMulti ℝ 2 ![e 0, e 1]))
        ⁅ω (ιMulti ℝ 2 ![e 0, e 2]), ω (ιMulti ℝ 2 ![e 0, e 3])⁆ := by
  obtain ⟨h23, h13, h12⟩ := o.apply_ιMulti_two_of_vectorFormHodgeStar_eq_self hkl he hω
  -- The trilinear form `B x ⁅y, z⁆` is invariant under cyclic permutations.
  have hc (x y z : V) : B y ⁅z, x⁆ = B x ⁅y, z⁆ := by
    rw [hB.eq, hinv.apply_lie_cyclic hB, hB.eq]
  rw [B.vectorFormInner_two_eq_sum_fin_four e]
  simp only [weitzenbockCurvatureTerm_apply_ιMulti e, Fin.sum_univ_four, ιMulti_two_swap_of_lt e,
    Fin.reduceLT, h23, h13, h12, ιMulti_two_self, map_neg, map_zero, lie_zero, zero_lie, lie_neg,
    neg_lie, map_add, map_sub, neg_neg]
  generalize ω (ιMulti ℝ 2 ![e 0, e 1]) = a
  generalize ω (ιMulti ℝ 2 ![e 0, e 2]) = b
  generalize ω (ιMulti ℝ 2 ![e 0, e 3]) = c
  have h₁ : B b ⁅c, a⁆ = B a ⁅b, c⁆ := hc a b c
  have h₂ : B c ⁅a, b⁆ = B a ⁅b, c⁆ := (hc b c a).trans (hc a b c)
  have h₃ : B a ⁅c, b⁆ = -B a ⁅b, c⁆ := by rw [← lie_skew, map_neg]
  have h₄ : B b ⁅a, c⁆ = -B a ⁅b, c⁆ := by rw [← lie_skew, map_neg, h₁]
  have h₅ : B c ⁅b, a⁆ = -B a ⁅b, c⁆ := by rw [← lie_skew, map_neg, h₂]
  simp only [h₁, h₂, h₃, h₄, h₅, LinearMap.neg_apply]
  ring

/-- **Only the self-dual part acts on self-dual forms**: in dimension four, `𝔉_{F⁺}(ω) = 𝔉_F(ω)`
for every `F` and every self-dual `ω`. -/
theorem weitzenbockCurvatureTerm_vectorFormSelfDualPart (F : ⋀[ℝ]^2 E →ₗ[ℝ] V)
    {ω : ⋀[ℝ]^2 E →ₗ[ℝ] V} (hω : o.vectorFormHodgeStar hkl ω = ω) :
    weitzenbockCurvatureTerm (o.vectorFormSelfDualPart hkl F) ω = weitzenbockCurvatureTerm F ω := by
  conv_rhs => rw [← o.vectorFormSelfDualPart_add_vectorFormAntiSelfDualPart hkl F]
  rw [map_add, LinearMap.add_apply,
    weitzenbockCurvatureTerm_eq_zero_of_vectorFormHodgeStar_eq_neg hkl
      (o.vectorFormHodgeStar_vectorFormAntiSelfDualPart even_two hkl F) hω, add_zero]

/-- The arithmetic–geometric mean inequality in the form used for the cubic bound:
`24 √p √q √r ≤ (2 √6 / 3) (2 (p + q + r))^{3/2}` for `p, q, r ≥ 0`. -/
private theorem mul_sqrt_mul_sqrt_mul_sqrt_le {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    24 * (√p * √q * √r) ≤ 2 * √6 / 3 * √(2 * (p + q + r)) ^ 3 := by
  have hs : 0 ≤ p + q + r := by positivity
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
  calc (24 * (√p * √q * √r)) ^ 2 = 576 * (√p ^ 2 * √q ^ 2 * √r ^ 2) := by ring
    _ = 576 * (p * q * r) := by rw [Real.sq_sqrt hp, Real.sq_sqrt hq, Real.sq_sqrt hr]
    _ ≤ 64 / 3 * (p + q + r) ^ 3 := by
      nlinarith [mul_nonneg hs (sq_nonneg (p - q)), mul_nonneg hs (sq_nonneg (q - r)),
        mul_nonneg hs (sq_nonneg (r - p)), mul_nonneg hp (sq_nonneg (q - r)),
        mul_nonneg hq (sq_nonneg (r - p)), mul_nonneg hr (sq_nonneg (p - q))]
    _ = (2 * √6 / 3 * √(2 * (p + q + r)) ^ 3) ^ 2 := by
      rw [show (2 * √6 / 3 * √(2 * (p + q + r)) ^ 3) ^ 2 =
          4 * √6 ^ 2 / 9 * (√(2 * (p + q + r)) ^ 2) ^ 3 by ring,
        Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
      ring

/-- **The cubic bound**: in dimension four, for a positive definite `ad`-invariant inner product `B`
on a finite-dimensional real Lie algebra `V`, with norm `γ₀` of the Lie bracket, every self-dual
`V`-valued two-form satisfies `|⟨ω, 𝔉_ω(ω)⟩| ≤ (2√6/3) γ₀ |ω|³`. -/
theorem abs_vectorFormInner_weitzenbockCurvatureTerm_le [FiniteDimensional ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (hB' : B.toQuadraticMap.PosDef)
    (hinv : B.lieInvariant V) {ω : ⋀[ℝ]^2 E →ₗ[ℝ] V} (hω : o.vectorFormHodgeStar hkl ω = ω) :
    |vectorFormInner B 2 ω (weitzenbockCurvatureTerm ω ω)| ≤
      2 * √6 / 3 * B.toQuadraticMap.lieBracketNorm * √(vectorFormInner B 2 ω ω) ^ 3 := by
  let e := o.finOrthonormalBasis (by norm_num) (Fact.out : finrank ℝ E = 4)
  have he : e.toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
  rw [vectorFormInner_weitzenbockCurvatureTerm_of_vectorFormHodgeStar_eq_self hkl he hB hinv hω,
    o.vectorFormInner_self_of_vectorFormHodgeStar_eq_self hkl he B hω]
  generalize ω (ιMulti ℝ 2 ![e 0, e 1]) = a
  generalize ω (ιMulti ℝ 2 ![e 0, e 2]) = b
  generalize ω (ιMulti ℝ 2 ![e 0, e 3]) = c
  have hnn (x : V) : 0 ≤ B x x := hB'.nonneg x
  -- Cauchy–Schwarz and the bracket bound: `|⟨a, ⁅b, c⁆⟩| ≤ γ₀ |a| |b| |c|`.
  have hCS : |B a ⁅b, c⁆| ≤ √(B a a) * √(B ⁅b, c⁆ ⁅b, c⁆) := by
    rw [← Real.sqrt_mul (hnn a), ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt <|
      B.apply_sq_le_of_symm hnn (LinearMap.BilinForm.isSymm_iff.mp hB) _ _
  have hbr : √(B ⁅b, c⁆ ⁅b, c⁆) ≤ B.toQuadraticMap.lieBracketNorm * √(B b b) * √(B c c) :=
    QuadraticMap.sqrt_apply_lie_le hB' b c
  have hγ := QuadraticMap.lieBracketNorm_nonneg B.toQuadraticMap
  calc |-24 * B a ⁅b, c⁆| = 24 * |B a ⁅b, c⁆| := by rw [abs_mul]; norm_num
    _ ≤ 24 * (√(B a a) * (B.toQuadraticMap.lieBracketNorm * √(B b b) * √(B c c))) := by
      gcongr
      exact hCS.trans (mul_le_mul_of_nonneg_left hbr (Real.sqrt_nonneg _))
    _ = B.toQuadraticMap.lieBracketNorm * (24 * (√(B a a) * √(B b b) * √(B c c))) := by ring
    _ ≤ B.toQuadraticMap.lieBracketNorm *
          (2 * √6 / 3 * √(2 * (B a a + B b b + B c c)) ^ 3) :=
      mul_le_mul_of_nonneg_left (mul_sqrt_mul_sqrt_mul_sqrt_le (hnn a) (hnn b) (hnn c)) hγ
    _ = _ := by ring

end FourDimensional

namespace CompactMatrixStructureGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (S : CompactMatrixStructureGroup n)
  [Fact (finrank ℝ E = 4)] {o : Orientation ℝ E (Fin 4)} (hkl : 2 + 2 = finrank ℝ E)

/-- **The cubic bound for a structure group**: in dimension four, every self-dual two-form `ω`
with values in the Lie algebra `𝔤` of a compact matrix structure group satisfies
`|⟨ω, 𝔉_ω(ω)⟩| ≤ (2√6/3) γ₀ |ω|³`, where `γ₀` is the structure constant of `𝔤`. -/
theorem abs_vectorFormInner_weitzenbockCurvatureTerm_le
    {ω : ⋀[ℝ]^2 E →ₗ[ℝ] S.group.matrixLieAlgebra} (hω : o.vectorFormHodgeStar hkl ω = ω) :
    |vectorFormInner S.innerForm 2 ω (weitzenbockCurvatureTerm ω ω)| ≤
      2 * √6 / 3 * S.innerForm.toQuadraticMap.lieBracketNorm *
        √(vectorFormInner S.innerForm 2 ω ω) ^ 3 :=
  TauCeti.abs_vectorFormInner_weitzenbockCurvatureTerm_le hkl S.isSymm_innerForm
    S.posDef_innerForm S.lieInvariant_innerForm hω

end CompactMatrixStructureGroup

end TauCeti
