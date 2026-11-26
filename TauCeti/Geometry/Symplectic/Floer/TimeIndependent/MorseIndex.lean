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
`ω = Im ⟪·, ·⟫`, and let `H : F → ℝ` be an autonomous Hamiltonian. A critical point `p` of `H` is
a rest point of `X_H`, so the constant loop at `p` is a one-periodic orbit of `H`. This file
computes the Fredholm index of the Sobolev realization
`D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` (`TauCeti.SymplecticForm.floerSobolevOperator`) of the
linearized Floer operator along any cylinder `u` running from the constant orbit at `p₋` to the
constant orbit at `p₊`, for any Floer data `(J, K_s, K_t)` with compatible almost complex
structures which equal the Floer data of `H` near the ends:

`ind D_u = ind_{p₊}(H) - ind_{p₋}(H)`

(`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_morseIndex_sub_morseIndex`), where
`ind_p(H)` is the Morse index (`TauCeti.morseIndex`). The hypotheses are that the two constant
orbits are nondegenerate fixed points of the time-one map of `H`, and that `H` is small along the
segment from `p₋` to `p₊`: `‖dX_H‖ ≤ a < 2π` there. The cylinder `u` need not solve the Floer
equation, and neither `u` nor the data need be independent of `s` or `t` away from the ends.

In the grading `μ(p) = ind_p(H) - n` of the constant orbits of a `C²`-small Morse Hamiltonian on
a space of complex dimension `n`, the grading by minus the Conley–Zehnder index of their
linearized flows
(`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_card_sub_morseIndex`), the index is
`μ(p₊) - μ(p₋)`.

The proof compares `D_u` with the operator along the time-independent cylinder
`(s, t) ↦ γ(s)` over the path `γ(s) = p₋ + β(s) (p₊ - p₋)` (`TauCeti.smoothSegmentPath`), where
`β` is a smooth transition from `0` to `1`.

* The index does not depend on the almost complex structures and the Hamiltonian terms away from
  the ends (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical_data`), nor on the
  map beyond its asymptotic orbits
  (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical`), so `D_u` has the index
  of the operator of the data `(i, 0, H)` along `(s, t) ↦ γ(s)`.
* Along a time-independent cylinder of a Hamiltonian with `‖dX_H‖ ≤ a < 2π`, the index is that
  of the Morse operator `ζ ↦ ζ' - i dX_H(γ) ζ`, namely `dim E⁻(p₋) - dim E⁻(p₊)`, where `E⁻(p)` is
  the sum of the eigenspaces of `-i dX_H(p)` at negative eigenvalues
  (`index_floerSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank`, in the namespace
  `TauCeti.SymplecticForm`).
  The path `γ` need not be a gradient line.
* For the metric `Re ⟪·, ·⟫`, `i dX_H(p)` is the Hessian of `H` at `p`
  (`TauCeti.SymplecticForm.apply_fderiv_hamiltonianVectorField_eq_hessianOperator`), so `E⁻(p)` is
  the positive spectral subspace of the Hessian, of dimension `2n - ind_p(H)` at a nondegenerate
  critical point
  (`TauCeti.SymplecticForm.finrank_pointSpectralSubspace_add_morseIndex`).
  A nondegenerate constant orbit sits at a nondegenerate critical point
  (`TauCeti.SymplecticForm.isNondegenerateCriticalPoint_of_isNondegenerateFixedPt'`).

So the index of a Floer cylinder between the constant orbits of a small Hamiltonian is the
expected dimension of the space of gradient lines of `H` from `p₋` to `p₊`: a time-independent
solution satisfies `γ' = ∇H`, and rises from `p₋` to `p₊`.

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
  {ω : SymplecticForm F} {H : F → ℝ}

/-- Along the time-independent cylinder `(s, t) ↦ γ(s)` over the path `γ` from `p₋` to `p₊` along
the segment, the operator of the data `(i, 0, H)` has index `ind_{p₊}(H) - ind_{p₋}(H)`, if
`‖dX_H‖ ≤ a < 2π` on the segment. -/
private theorem index_floerSobolevOperator_smoothSegmentPath
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) {a : ℝ} (ha : a < 2 * Real.pi)
    {pm pp : F}
    (haH : ∀ y ∈ segment ℝ pm pp, ‖fderiv ℝ (ω.hamiltonianVectorField H) y‖ ≤ a)
    (hpm : IsNondegenerateCriticalPoint H pm) (hpp : IsNondegenerateCriticalPoint H pp) :
    (ω.floerSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ smoothSegmentPath pm pp z.1)).index =
      (morseIndex H pp : ℤ) - morseIndex H pm := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hg := ω.apply_ofComplexModule_eq_inner hω
  rw [index_floerSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank hω hH
    (contDiff_smoothSegmentPath (n := 0) pm pp).continuous ha
    (fun s ↦ haH _ (smoothSegmentPath_mem_segment pm pp s))
    (tendsto_const_nhds.congr' (eventuallyEq_smoothSegmentPath_atBot pm pp).symm)
    (tendsto_const_nhds.congr' (eventuallyEq_smoothSegmentPath_atTop pm pp).symm)
    (injective_fderiv_hamiltonianVectorField_of_isNondegenerateCriticalPoint hg hpm)
    (injective_fderiv_hamiltonianVectorField_of_isNondegenerateCriticalPoint hg hpp)]
  have hm := finrank_pointSpectralSubspace_add_morseIndex hg hpm
  have hp := finrank_pointSpectralSubspace_add_morseIndex hg hpp
  omega

/-- **The index of the linearized Floer operator between critical points.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, and let
`H : F → ℝ` be a `C³` autonomous Hamiltonian whose Hamiltonian vector field is globally Lipschitz.
Let `p₋` and `p₊` be critical points of `H` whose constant orbits are nondegenerate fixed points of
the time-one map, and suppose that `‖dX_H‖ ≤ a < 2π` on the segment from `p₋` to `p₊`. Let the
Floer data `(J, K_s, K_t)` be `C¹` (with `C²` Hamiltonians) on the whole cylinder, compatible with
`ω` and cylindrical near the ends with the Hamiltonian `H` at both ends, and let `u` be a `C¹`
map whose loops converge uniformly to `p₋` at `-∞` and to `p₊` at `+∞`, with slice defects
`∂t u - X_H(u)` tending uniformly to zero there. Then the realization
`D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator has index
`ind_{p₊}(H) - ind_{p₋}(H)`, a difference of Morse indices. It is Fredholm by
`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`. -/
theorem index_floerSobolevOperator_eq_morseIndex_sub_morseIndex
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 3 H) {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ ↦ H)) {a : ℝ}
    (ha : a < 2 * Real.pi) {pm pp : F}
    (haH : ∀ y ∈ segment ℝ pm pp, ‖fderiv ℝ (ω.hamiltonianVectorField H) y‖ ≤ a)
    (hpm : fderiv ℝ H pm = 0)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (fun _ ↦ H) hX 0 1) pm)
    (hpp : fderiv ℝ H pp = 0)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (fun _ ↦ H) hX 0 1) pp)
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ}
    {Jm Jp : ℝ → F → AlmostComplexStructure F} {R : ℝ} {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp (fun _ ↦ H) (fun _ ↦ H) R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hu : ContDiff ℝ 1 u)
    (hum : TendstoUniformlyOn (fun s t ↦ u (s, t)) (fun _ ↦ pm) atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun _ ↦ ω.hamiltonianVectorField H) u (s, t)) 0 atBot (Icc 0 1))
    (hup : TendstoUniformlyOn (fun s t ↦ u (s, t)) (fun _ ↦ pp) atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun _ ↦ ω.hamiltonianVectorField H) u (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u).index = (morseIndex H pp : ℤ) - morseIndex H pm := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hH₂ : ContDiff ℝ 2 H := hH.of_le (by norm_num)
  have hHu : ContDiff ℝ 3 (uncurry fun (_ : ℝ) ↦ H) := hH.comp contDiff_snd
  have hHu₂ : ContDiff ℝ 2 (uncurry fun (_ : ℝ) ↦ H) := hH₂.comp contDiff_snd
  have hXz (p : F) (hp : fderiv ℝ H p = 0) : ω.hamiltonianVectorField H p = 0 :=
    (ω.hamiltonianVectorField_eq_zero_iff H p).2 hp
  have hx (p : F) (hp : fderiv ℝ H p = 0) (t : ℝ) :
      HasDerivAt (fun _ : ℝ ↦ p) (ω.hamiltonianVectorField H p) t := by
    rw [hXz p hp]
    exact hasDerivAt_const t p
  set Jc := AlmostComplexStructure.ofComplexModule F
  have hJc₀ (z : ℝ × ℝ) (y : F) : ω.Compatible ((fun _ _ ↦ Jc : ℝ × ℝ → F → _) z y) :=
    ω.compatible_ofComplexModule_of_forall_eq_im_inner hω
  -- The data `(i, 0, H)` are cylindrical near the ends along every map.
  have hcyl₀ (v : ℝ × ℝ → F) := Floer.isCylindricalNearEnds_comp_snd (J := fun _ _ ↦ Jc) (R := 0)
    contDiff_const hHu₂ v
  -- Along `u`, the operator of the data `(i, 0, H)` is Fredholm, with the index of `D_u`.
  have h₀ := ω.isFredholm_floerSobolevOperator_of_compatible hω (J := fun _ _ ↦ Jc) contDiff_const
    (fun _ _ ↦ hJc₀ 0 0) hX hHu (fun _ ↦ rfl) (hx pm hpm) (fun _ ↦ rfl) hndm (hx pp hpp)
    (fun _ ↦ rfl) hndp hu hum hδm hup hδp
  have hdata := index_floerSobolevOperator_eq_of_cylindrical_data ω (hcyl₀ u) hcyl contDiff_const
    contDiff_const (hHu₂.comp (contDiff_fst.snd.prodMk contDiff_snd)) hJ hKs hKt hJc₀ hJc hu hX
    (hx pm hpm) hndm hum hδm hX (hx pp hpp) hndp hup hδp h₀
  -- The comparison cylinder over the path `γ` from `pm` to `pp` along the segment.
  have hγ := contDiff_smoothSegmentPath (n := 1) pm pp
  have hγm := tendstoUniformlyOn_comp_fst_and_sliceDefect hγ
    (eventuallyEq_smoothSegmentPath_atBot pm pp) (fun _ ↦ hXz pm hpm)
  have hγp := tendstoUniformlyOn_comp_fst_and_sliceDefect hγ
    (eventuallyEq_smoothSegmentPath_atTop pm pp) (fun _ ↦ hXz pp hpp)
  have hγu : ContDiff ℝ 1 fun z : ℝ × ℝ ↦ smoothSegmentPath pm pp z.1 := hγ.comp contDiff_fst
  have hmap := index_floerSobolevOperator_eq_of_cylindrical ω (hcyl₀ u) contDiff_const
    contDiff_const (hHu₂.comp (contDiff_fst.snd.prodMk contDiff_snd)) hJc₀ hu hγu hX (hx pm hpm)
    hndm hum hδm hγm.1 hγm.2 hX (hx pp hpp) hndp hup hδp hγp.1 hγp.2 h₀
  rw [hdata, ← hmap]
  exact index_floerSobolevOperator_smoothSegmentPath hω hH₂ ha haH
    (ω.isNondegenerateCriticalPoint_of_isNondegenerateFixedPt' hH₂ hpm hX hndm)
    (ω.isNondegenerateCriticalPoint_of_isNondegenerateFixedPt' hH₂ hpp hX hndp)

end Unitary

end TauCeti.SymplecticForm
