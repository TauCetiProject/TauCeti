/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Fredholm
import TauCeti.Analysis.SpecialFunctions.SmoothSegmentPath
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Index
import TauCeti.Geometry.Symplectic.Hamiltonian.ConstantOrbit
import TauCeti.Geometry.Symplectic.Hamiltonian.Hessian
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The index of the linearized Floer operator between critical points

Let `F` be a finite-dimensional complex inner product space with symplectic form
`ω = Im ⟪·, ·⟫`, and let `H₋, H₊ : F → ℝ` be autonomous Hamiltonians. A critical point `p` of a
Hamiltonian `H` is a rest point of `X_H`, so the constant loop at `p` is a one-periodic orbit of
`H`. This file computes the Fredholm index of the Sobolev realization
`D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` (`TauCeti.SymplecticForm.floerSobolevOperator`) of the
linearized Floer operator along any cylinder `u` running from the constant orbit at a critical
point `p₋` of `H₋` to the constant orbit at a critical point `p₊` of `H₊`, for any Floer data
`(J, K_s, K_t)` with compatible almost complex structures which equal the Floer data of `H₋` near
`-∞` and those of `H₊` near `+∞`, such as continuation data from `H₋` to `H₊`:

`ind D_u = ind_{p₊}(H₊) - ind_{p₋}(H₋)`

(`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_morseIndex_sub_morseIndex`), where
`ind_p(H)` is the Morse index (`TauCeti.morseIndex`). The hypotheses are that the two constant
orbits are nondegenerate fixed points of the time-one maps, and that the Hamiltonians are small at
their critical points: `‖dX_{H₋}(p₋)‖ < 2π` and `‖dX_{H₊}(p₊)‖ < 2π`. The cylinder `u` need not
solve the Floer equation, and neither `u` nor the data need be independent of `s` or `t` away
from the ends. The case `H₋ = H₊` is a cylinder of a single autonomous Hamiltonian.

In the grading `μ(p) = ind_p(H) - n` of the constant orbits of a `C²`-small Morse Hamiltonian on
a space of complex dimension `n`, the grading by minus the Conley–Zehnder index of their
linearized flows
(`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_card_sub_morseIndex`), the index is
`μ(p₊) - μ(p₋)`, with the gradings of `H₊` and of `H₋` respectively.

The proof compares `D_u` with the operator along the time-independent cylinder
`(s, t) ↦ γ(s)` over the path `γ(s) = p₋ + ψ(s) (p₊ - p₋)` (`TauCeti.smoothSegmentPath`), where
`ψ` is a smooth transition from `0` to `1`, for the Hamiltonians
`K_s(y) = (1 - ψ(s)) H₋(y + p₋ - γ(s)) + ψ(s) H₊(y + p₊ - γ(s))`, which are `H₋` for `s ≤ 0` and
`H₊` for `s ≥ 1`.

* The index does not depend on the almost complex structures and the Hamiltonian terms away from
  the ends (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical_data`), nor on the
  map beyond its asymptotic orbits
  (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical`), so `D_u` has the index
  of the operator of the data `(i, 0, K)` along `(s, t) ↦ γ(s)`.
* A translate of a Hamiltonian has the translated vector field
  (`TauCeti.SymplecticForm.hamiltonianVectorField_comp_add_right`), so along `γ` the derivative
  `dX_{K_s}(γ(s)) = (1 - ψ(s)) dX_{H₋}(p₋) + ψ(s) dX_{H₊}(p₊)` interpolates between the two ends
  and has norm less than `2π`. Along a time-independent cylinder of Hamiltonians depending on `s`
  with `‖dX_{K_s}(γ(s))‖ ≤ a < 2π`, the index is that of the Morse operator
  `ζ ↦ ζ' - i dX_{K_s}(γ) ζ`, namely `dim E⁻(H₋, p₋) - dim E⁻(H₊, p₊)`, where `E⁻(G, p)` is the
  sum of the eigenspaces of `-i dX_G(p)` at negative eigenvalues
  (`index_floerSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank`, in the namespace
  `TauCeti.SymplecticForm`).
* For the metric `Re ⟪·, ·⟫`, `i dX_G(p)` is the Hessian of `G` at `p`
  (`TauCeti.SymplecticForm.apply_fderiv_hamiltonianVectorField_eq_hessianOperator`), so `E⁻(G, p)`
  is the positive spectral subspace of the Hessian, of dimension `2n - ind_p(G)` at a
  nondegenerate critical point
  (`TauCeti.SymplecticForm.finrank_pointSpectralSubspace_add_morseIndex`).
  A nondegenerate constant orbit sits at a nondegenerate critical point
  (`TauCeti.SymplecticForm.isNondegenerateCriticalPoint_of_isNondegenerateFixedPt'`).

So the index of a Floer cylinder between the constant orbits of small Hamiltonians is the
difference of the Morse indices; for a single Hamiltonian it is the expected dimension of the
space of gradient lines of `H` from `p₋` to `p₊`: a time-independent solution satisfies
`γ' = ∇H`, and rises from `p₋` to `p₊`.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

open Filter Function Set
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

section Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The loops of the cylinder `(s, t) ↦ γ(s)` over a path `γ` which is eventually constant along a
filter converge uniformly to the constant loop, and their slice defects for a vector field `X`
vanishing at the constant converge uniformly to zero. -/
private theorem tendstoUniformlyOn_comp_fst_and_sliceDefect {X : ℝ → E → E} {γ : ℝ → E}
    (hγ : ContDiff ℝ 1 γ) {l : Filter ℝ} {p : E} (hl : γ =ᶠ[l] fun _ ↦ p)
    (hX : ∀ t, X t p = 0) :
    TendstoUniformlyOn (fun s (t : ℝ) ↦ γ (s, t).1) (fun _ ↦ p) l (Icc 0 1) ∧
      TendstoUniformlyOn (fun s t ↦ sliceDefect X (fun z : ℝ × ℝ ↦ γ z.1) (s, t)) 0 l
        (Icc 0 1) := by
  refine ⟨(tendstoUniformlyOn_const _ l _).congr (hl.mono fun s hs t _ ↦ hs.symm),
    (tendstoUniformlyOn_const _ l _).congr (hl.mono fun s hs t _ ↦ ?_)⟩
  -- The cylinder does not depend on `t`, so its slice defect is `-X(t, γ(s))`.
  have hd : HasFDerivAt (fun z : ℝ × ℝ ↦ γ z.1)
      ((fderiv ℝ γ s).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) (s, t) :=
    ((hγ.differentiable one_ne_zero s).hasFDerivAt.comp (s, t) (hasFDerivAt_fst (p := (s, t))))
  simp [sliceDefect_def, hd.fderiv, hs, hX]

end Path

section Unitary

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {ω : SymplecticForm F} {Hm Hp : F → ℝ} {pm pp : F}

/-- The comparison Hamiltonians
`K_s(y) = (1 - ψ(s)) H₋(y + p₋ - γ(s)) + ψ(s) H₊(y + p₊ - γ(s))` along the path
`γ = smoothSegmentPath p₋ p₊`, where `ψ` is the smooth transition. They are `H₋` for `s ≤ 0` and
`H₊` for `s ≥ 1`, and along `γ` the derivative of their vector fields interpolates linearly between
`dX_{H₋}(p₋)` and `dX_{H₊}(p₊)`. -/
private noncomputable def comparisonHamiltonian (Hm Hp : F → ℝ) (pm pp : F) (s : ℝ) (y : F) : ℝ :=
  (1 - Real.smoothTransition s) * Hm (y + (pm - smoothSegmentPath pm pp s)) +
    Real.smoothTransition s * Hp (y + (pp - smoothSegmentPath pm pp s))

omit [FiniteDimensional ℂ F] in
private theorem contDiff_comparisonHamiltonian (hHm : ContDiff ℝ 2 Hm) (hHp : ContDiff ℝ 2 Hp) :
    ContDiff ℝ 2 (uncurry (comparisonHamiltonian Hm Hp pm pp)) := by
  have hψ : ContDiff ℝ 2 fun q : ℝ × F ↦ Real.smoothTransition q.1 :=
    Real.smoothTransition.contDiff.comp contDiff_fst
  have hγ : ContDiff ℝ 2 fun q : ℝ × F ↦ smoothSegmentPath pm pp q.1 :=
    (contDiff_smoothSegmentPath pm pp).comp contDiff_fst
  exact ((contDiff_const.sub hψ).mul (hHm.comp (contDiff_snd.add (contDiff_const.sub hγ)))).add
    (hψ.mul (hHp.comp (contDiff_snd.add (contDiff_const.sub hγ))))

omit [FiniteDimensional ℂ F] in
private theorem comparisonHamiltonian_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    comparisonHamiltonian Hm Hp pm pp s = Hm := by
  funext y
  simp [comparisonHamiltonian, Real.smoothTransition.zero_of_nonpos hs,
    smoothSegmentPath_of_nonpos _ _ hs]

omit [FiniteDimensional ℂ F] in
private theorem comparisonHamiltonian_of_one_le {s : ℝ} (hs : 1 ≤ s) :
    comparisonHamiltonian Hm Hp pm pp s = Hp := by
  funext y
  simp [comparisonHamiltonian, Real.smoothTransition.one_of_one_le hs,
    smoothSegmentPath_of_one_le _ _ hs]

/-- Along `γ = smoothSegmentPath p₋ p₊`, the linearized vector field of the comparison
Hamiltonian is `(1 - ψ(s)) dX_{H₋}(p₋) + ψ(s) dX_{H₊}(p₊)`. -/
private theorem fderiv_hamiltonianVectorField_comparisonHamiltonian (hHm : ContDiff ℝ 2 Hm)
    (hHp : ContDiff ℝ 2 Hp) (s : ℝ) :
    fderiv ℝ (ω.hamiltonianVectorField (comparisonHamiltonian Hm Hp pm pp s))
        (smoothSegmentPath pm pp s) =
      (1 - Real.smoothTransition s) • fderiv ℝ (ω.hamiltonianVectorField Hm) pm +
        Real.smoothTransition s • fderiv ℝ (ω.hamiltonianVectorField Hp) pp := by
  have hK : comparisonHamiltonian Hm Hp pm pp s = fun y ↦
      (1 - Real.smoothTransition s) * Hm (y + (pm - smoothSegmentPath pm pp s)) +
        Real.smoothTransition s * Hp (y + (pp - smoothSegmentPath pm pp s)) := rfl
  have hHm' : ContDiff ℝ 2 fun y ↦ Hm (y + (pm - smoothSegmentPath pm pp s)) :=
    hHm.comp (contDiff_id.add contDiff_const)
  have hHp' : ContDiff ℝ 2 fun y ↦ Hp (y + (pp - smoothSegmentPath pm pp s)) :=
    hHp.comp (contDiff_id.add contDiff_const)
  rw [hK, ω.fderiv_hamiltonianVectorField_const_mul_add_const_mul hHm' hHp',
    ω.hamiltonianVectorField_comp_add_right, ω.hamiltonianVectorField_comp_add_right,
    fderiv_comp_add_right, fderiv_comp_add_right, add_sub_cancel, add_sub_cancel]

/-- Along the time-independent cylinder `(s, t) ↦ γ(s)` over the path `γ` from `p₋` to `p₊` along
the segment, the operator of the data `(i, 0, K)` of the comparison Hamiltonians has index
`ind_{p₊}(H₊) - ind_{p₋}(H₋)`, if `‖dX_{H₋}(p₋)‖ < 2π` and `‖dX_{H₊}(p₊)‖ < 2π`. -/
private theorem index_floerSobolevOperator_comparisonHamiltonian
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hHm : ContDiff ℝ 2 Hm) (hHp : ContDiff ℝ 2 Hp)
    (ham : ‖fderiv ℝ (ω.hamiltonianVectorField Hm) pm‖ < 2 * Real.pi)
    (hap : ‖fderiv ℝ (ω.hamiltonianVectorField Hp) pp‖ < 2 * Real.pi)
    (hpm : IsNondegenerateCriticalPoint Hm pm) (hpp : IsNondegenerateCriticalPoint Hp pp) :
    (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ comparisonHamiltonian Hm Hp pm pp z.1)
        (fun z ↦ smoothSegmentPath pm pp z.1)).index =
      (morseIndex Hp pp : ℤ) - morseIndex Hm pm := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hg := ω.apply_ofComplexModule_eq_inner hω
  set a := max ‖fderiv ℝ (ω.hamiltonianVectorField Hm) pm‖
    ‖fderiv ℝ (ω.hamiltonianVectorField Hp) pp‖
  -- Along `γ` the linearized vector fields are convex combinations of those at `p₋` and `p₊`.
  have haγ (s : ℝ) : ‖fderiv ℝ (ω.hamiltonianVectorField (comparisonHamiltonian Hm Hp pm pp s))
      (smoothSegmentPath pm pp s)‖ ≤ a := by
    rw [fderiv_hamiltonianVectorField_comparisonHamiltonian hHm hHp]
    have h0 := Real.smoothTransition.nonneg s
    have h1 := Real.smoothTransition.le_one s
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h1), Real.norm_of_nonneg h0]
    nlinarith [le_max_left ‖fderiv ℝ (ω.hamiltonianVectorField Hm) pm‖
      ‖fderiv ℝ (ω.hamiltonianVectorField Hp) pp‖, le_max_right
        ‖fderiv ℝ (ω.hamiltonianVectorField Hm) pm‖ ‖fderiv ℝ (ω.hamiltonianVectorField Hp) pp‖]
  rw [index_floerSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank hω
    (contDiff_comparisonHamiltonian hHm hHp) (contDiff_smoothSegmentPath (n := 0) pm pp).continuous
    (max_lt ham hap) haγ
    ((eventually_le_atBot 0).mono fun _ hs ↦ comparisonHamiltonian_of_nonpos hs)
    ((eventually_ge_atTop 1).mono fun _ hs ↦ comparisonHamiltonian_of_one_le hs)
    (tendsto_const_nhds.congr' (eventuallyEq_smoothSegmentPath_atBot pm pp).symm)
    (tendsto_const_nhds.congr' (eventuallyEq_smoothSegmentPath_atTop pm pp).symm)
    (injective_fderiv_hamiltonianVectorField_of_isNondegenerateCriticalPoint hg hpm)
    (injective_fderiv_hamiltonianVectorField_of_isNondegenerateCriticalPoint hg hpp)]
  have hm := finrank_pointSpectralSubspace_add_morseIndex hg hpm
  have hp := finrank_pointSpectralSubspace_add_morseIndex hg hpp
  omega

/-- **The index of the linearized Floer operator between critical points.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, and let
`H₋, H₊ : F → ℝ` be `C³` autonomous Hamiltonians whose Hamiltonian vector fields are globally
Lipschitz. Let `p₋` be a critical point of `H₋` and `p₊` one of `H₊`, whose constant orbits are
nondegenerate fixed points of the time-one maps, and suppose that `‖dX_{H₋}(p₋)‖ < 2π` and
`‖dX_{H₊}(p₊)‖ < 2π`. Let the Floer data `(J, K_s, K_t)` be `C¹` (with `C²` Hamiltonians) on the
whole cylinder, compatible with `ω` and cylindrical near the ends with the Hamiltonian `H₋` at
`-∞` and `H₊` at `+∞`, such as continuation data from `H₋` to `H₊`, and let `u` be a `C¹` map whose
loops converge uniformly to `p₋` at `-∞` and to `p₊` at `+∞`, with slice defects
`∂t u - X_{H±}(u)` tending uniformly to zero there. Then the realization
`D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator has index
`ind_{p₊}(H₊) - ind_{p₋}(H₋)`, a difference of Morse indices. It is Fredholm by
`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`. -/
theorem index_floerSobolevOperator_eq_morseIndex_sub_morseIndex
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hHm : ContDiff ℝ 3 Hm) (hHp : ContDiff ℝ 3 Hp)
    {Km Kp : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension fun _ ↦ Hm))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension fun _ ↦ Hp))
    (ham : ‖fderiv ℝ (ω.hamiltonianVectorField Hm) pm‖ < 2 * Real.pi)
    (hap : ‖fderiv ℝ (ω.hamiltonianVectorField Hp) pp‖ < 2 * Real.pi)
    (hpm : fderiv ℝ Hm pm = 0)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (fun _ ↦ Hm) hXm 0 1)
      pm)
    (hpp : fderiv ℝ Hp pp = 0)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (fun _ ↦ Hp) hXp 0 1)
      pp)
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ}
    {Jm Jp : ℝ → F → AlmostComplexStructure F} {R : ℝ} {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp (fun _ ↦ Hm) (fun _ ↦ Hp) R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hu : ContDiff ℝ 1 u)
    (hum : TendstoUniformlyOn (fun s t ↦ u (s, t)) (fun _ ↦ pm) atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun _ ↦ ω.hamiltonianVectorField Hm) u (s, t)) 0 atBot (Icc 0 1))
    (hup : TendstoUniformlyOn (fun s t ↦ u (s, t)) (fun _ ↦ pp) atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun _ ↦ ω.hamiltonianVectorField Hp) u (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerSobolevOperator 2 (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u).index = (morseIndex Hp pp : ℤ) - morseIndex Hm pm := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hHm₂ : ContDiff ℝ 2 Hm := hHm.of_le (by norm_num)
  have hHp₂ : ContDiff ℝ 2 Hp := hHp.of_le (by norm_num)
  have hXz {G : F → ℝ} {p : F} (hp : fderiv ℝ G p = 0) : ω.hamiltonianVectorField G p = 0 :=
    (ω.hamiltonianVectorField_eq_zero_iff G p).2 hp
  have hx {G : F → ℝ} {p : F} (hp : fderiv ℝ G p = 0) (t : ℝ) :
      HasDerivAt (fun _ : ℝ ↦ p) (ω.hamiltonianVectorField G p) t := by
    rw [hXz hp]
    exact hasDerivAt_const t p
  set Jc := AlmostComplexStructure.ofComplexModule F
  have hJc₀ (z : ℝ × ℝ) (y : F) : ω.Compatible ((fun _ _ ↦ Jc : ℝ × ℝ → F → _) z y) :=
    ω.compatible_ofComplexModule_of_forall_eq_im_inner hω
  -- The comparison data `(i, 0, K)` are cylindrical near the ends, with `H₋` and `H₊` there.
  set K := comparisonHamiltonian Hm Hp pm pp
  have hKt₀ : ContDiff ℝ 2 (uncurry fun z : ℝ × ℝ ↦ K z.1) :=
    (contDiff_comparisonHamiltonian hHm₂ hHp₂).comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hcyl₀ (v : ℝ × ℝ → F) : Floer.IsCylindricalNearEnds (fun _ _ ↦ Jc) (fun _ _ ↦ 0)
      (fun z ↦ K z.1) (fun _ _ ↦ Jc) (fun _ _ ↦ Jc) (fun _ ↦ Hm) (fun _ ↦ Hp) 1 v :=
    { almostComplex_eq_of_le_neg := fun _ _ ↦ rfl
      almostComplex_eq_of_le := fun _ _ ↦ rfl
      hamiltonianS_eq_zero := fun _ _ ↦ rfl
      hamiltonianT_eq_of_le_neg := fun _ hz ↦ comparisonHamiltonian_of_nonpos (by linarith)
      hamiltonianT_eq_of_le := fun _ hz ↦ comparisonHamiltonian_of_one_le hz
      contDiffAt_almostComplex := fun _ ↦ contDiffAt_const
      contDiffAt_hamiltonianS := fun _ ↦ contDiffAt_const
      contDiffAt_hamiltonianT := fun _ ↦ hKt₀.contDiffAt }
  -- Along `u`, the operator of the comparison data is Fredholm, with the index of `D_u`.
  have h₀ := ω.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible hω (hcyl₀ u)
    contDiff_const contDiff_const hKt₀ hJc₀ hu hXm (hHm.comp contDiff_snd) (fun _ ↦ rfl) (hx hpm)
    (fun _ ↦ rfl) hndm hum hδm hXp (hHp.comp contDiff_snd) (fun _ ↦ rfl) (hx hpp) (fun _ ↦ rfl)
    hndp hup hδp
  have hdata := index_floerSobolevOperator_eq_of_cylindrical_data ω (hcyl₀ u) hcyl contDiff_const
    contDiff_const hKt₀ hJ hKs hKt hJc₀ hJc hu hXm (hx hpm) hndm hum hδm hXp (hx hpp) hndp hup hδp
    h₀
  -- The comparison cylinder over the path `γ` from `pm` to `pp` along the segment.
  have hγ := contDiff_smoothSegmentPath (n := 1) pm pp
  have hγm := tendstoUniformlyOn_comp_fst_and_sliceDefect hγ
    (eventuallyEq_smoothSegmentPath_atBot pm pp) (fun _ ↦ hXz hpm)
  have hγp := tendstoUniformlyOn_comp_fst_and_sliceDefect hγ
    (eventuallyEq_smoothSegmentPath_atTop pm pp) (fun _ ↦ hXz hpp)
  have hγu : ContDiff ℝ 1 fun z : ℝ × ℝ ↦ smoothSegmentPath pm pp z.1 := hγ.comp contDiff_fst
  have hmap := index_floerSobolevOperator_eq_of_cylindrical ω (hcyl₀ u) contDiff_const
    contDiff_const hKt₀ hJc₀ hu hγu hXm (hx hpm) hndm hum hδm hγm.1 hγm.2 hXp (hx hpp) hndp hup
    hδp hγp.1 hγp.2 h₀
  rw [hdata, ← hmap]
  exact index_floerSobolevOperator_comparisonHamiltonian hω hHm₂ hHp₂ ham hap
    (ω.isNondegenerateCriticalPoint_of_isNondegenerateFixedPt' hHm₂ hpm hXm hndm)
    (ω.isNondegenerateCriticalPoint_of_isNondegenerateFixedPt' hHp₂ hpp hXp hndp)

end Unitary

end TauCeti.SymplecticForm
