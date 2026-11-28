/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.Contractible
import TauCeti.Topology.Algebra.Module.ComplexSmulI
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# The tangent bundle of an almost complex manifold as a complex vector bundle

An almost complex structure `J` of any regularity `n` (in particular a continuous one) on a manifold
`M` modelled on a real normed space `E` is a continuous complex structure on the tangent bundle
(`TauCeti.ContMDiffAlmostComplexStructure.toContinuousComplexStructure`); a smooth almost complex
structure `J` is covered through `J.toContMDiff n`. Hence, when `E` is finite-dimensional, the
tangent spaces, with `J` as multiplication by `i`, form a complex vector bundle
`J.toContinuousComplexStructure.Fiber` over `M`, with model fibre any finite-dimensional complex
normed space `G` with `finrank ℝ E = 2 * finrank ℂ G`
(`TauCeti.Bundle.ContinuousComplexStructure.vectorPrebundle`), and its total space is the tangent
bundle (`TauCeti.Bundle.ContinuousComplexStructure.totalSpaceHomeomorph`).

Along a continuous map `f` from a contractible paracompact R₁ space, for instance a disc, this
complex vector bundle has a frame: real-linear isomorphisms `G ≃ T_(f y) M`, continuous into the
tangent bundle, carrying multiplication by `i` to `J`
(`TauCeti.ContMDiffAlmostComplexStructure.exists_continuous_frame`). Conversely, a real-linear
isomorphism `G ≃ T_b M` carrying multiplication by `i` to `J` is a complex-linear isomorphism onto
the fibre of this complex vector bundle at `b`
(`TauCeti.ContMDiffAlmostComplexStructure.complexFrame`). Two such frames along a map differ by a
continuous family of complex automorphisms of `G`
(`TauCeti.SmoothAlmostComplexStructure.exists_continuous_complex_frame_change`).

For a symplectic manifold with a compatible almost complex structure this is the complex vector
bundle `(TM, J)` whose first Chern class is the first Chern class of `M`; its pairing with spheres
is the Chern number entering the grading of capped Hamiltonian Floer theory.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 2.1.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.ContMDiffAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ∞}

/-- An almost complex structure of any regularity, as a continuous complex structure on the tangent
bundle. -/
def toContinuousComplexStructure (J : ContMDiffAlmostComplexStructure I n M) :
    Bundle.ContinuousComplexStructure E (TangentSpace I : M → Type _) where
  toFun := J.toEndomorphism
  comp_self := J.square_neg
  continuous := J.toEndomorphism.contMDiff.continuous

@[simp]
theorem toContinuousComplexStructure_apply (J : ContMDiffAlmostComplexStructure I n M) (x : M)
    (v : TangentSpace I x) : J.toContinuousComplexStructure x v = J x v := (rfl)

/-- The pointwise almost complex structures of `J.toContinuousComplexStructure`, which give the
complex structures of its fibres, are those of `J`. -/
@[simp]
theorem toContinuousComplexStructure_almostComplexStructureAt
    (J : ContMDiffAlmostComplexStructure I n M) (x : M) :
    J.toContinuousComplexStructure.almostComplexStructureAt x = J.almostComplexStructureAt x := by
  ext v
  rw [Bundle.ContinuousComplexStructure.almostComplexStructureAt_apply,
    toContinuousComplexStructure_apply, almostComplexStructureAt_apply]


section Frame

variable [FiniteDimensional ℝ E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [FiniteDimensional ℂ G] {Y : Type*} [TopologicalSpace Y] {f : Y → M}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℂ G] in
/-- A real-linear isomorphism `χ : G ≃ T_b M` carrying multiplication by `i` to `J`, as a
complex-linear isomorphism onto the fibre at `b` of the complex vector bundle `(TM, J)`. -/
def complexFrame (J : ContMDiffAlmostComplexStructure I n M) {b : M}
    (χ : G ≃L[ℝ] TangentSpace I b) (hχ : ∀ v, χ (Complex.I • v) = J b (χ v)) :
    G ≃L[ℂ] J.toContinuousComplexStructure.Fiber b :=
  (χ.trans (J.toContinuousComplexStructure.fiberEquiv b).symm).complexOfMapISmul fun v ↦
    (J.toContinuousComplexStructure.fiberEquiv b).injective <| by
      rw [Bundle.ContinuousComplexStructure.fiberEquiv_I_smul, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
        ContinuousLinearEquiv.apply_symm_apply, hχ, toContinuousComplexStructure_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℂ G] in
/-- The complex frame `J.complexFrame χ hχ` is `χ`, followed by the identification of `T_b M` with
the fibre of `(TM, J)` at `b`. -/
@[simp]
theorem complexFrame_apply (J : ContMDiffAlmostComplexStructure I n M) {b : M}
    (χ : G ≃L[ℝ] TangentSpace I b) (hχ : ∀ v, χ (Complex.I • v) = J b (χ v)) (v : G) :
    J.complexFrame χ hχ v = (J.toContinuousComplexStructure.fiberEquiv b).symm (χ v) :=
  ContinuousLinearEquiv.complexOfMapISmul_apply _ _ v

/-- The complex frame `J.complexFrame χ hχ` is `χ`, read in the tangent bundle. -/
theorem totalSpaceHomeomorph_mk_complexFrame (J : ContMDiffAlmostComplexStructure I n M)
    [Fact (Module.finrank ℝ E = 2 * Module.finrank ℂ G)] {b : M} (χ : G ≃L[ℝ] TangentSpace I b)
    (hχ : ∀ v, χ (Complex.I • v) = J b (χ v)) (v : G) :
    J.toContinuousComplexStructure.totalSpaceHomeomorph G
      (TotalSpace.mk' G b (J.complexFrame χ hχ v)) = (⟨b, χ v⟩ : TangentBundle I M) := by
  rw [Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply, complexFrame_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Complex frames take the same value in the total space of `(TM, J)` wherever the real frames
they come from take the same value in the tangent bundle. -/
theorem mk_complexFrame_eq_mk_complexFrame (J : ContMDiffAlmostComplexStructure I n M)
    [Fact (Module.finrank ℝ E = 2 * Module.finrank ℂ G)] {b b' : M}
    {χ : G ≃L[ℝ] TangentSpace I b} {χ' : G ≃L[ℝ] TangentSpace I b'}
    (hχ : ∀ v, χ (Complex.I • v) = J b (χ v)) (hχ' : ∀ v, χ' (Complex.I • v) = J b' (χ' v))
    {v v' : G} (h : (⟨b, χ v⟩ : TangentBundle I M) = ⟨b', χ' v'⟩) :
    TotalSpace.mk' G b (J.complexFrame χ hχ v) =
      TotalSpace.mk' G b' (J.complexFrame χ' hχ' v') := by
  refine (J.toContinuousComplexStructure.totalSpaceHomeomorph G).injective ?_
  rw [totalSpaceHomeomorph_mk_complexFrame, totalSpaceHomeomorph_mk_complexFrame, h]

/-- A family of complex frames along a map `f` is continuous into the total space of `(TM, J)`
when the real frames it comes from are continuous into the tangent bundle. -/
theorem continuous_complexFrame (J : ContMDiffAlmostComplexStructure I n M)
    [Fact (Module.finrank ℝ E = 2 * Module.finrank ℂ G)] {χ : ∀ y, G ≃L[ℝ] TangentSpace I (f y)}
    (hχ : Continuous fun q : Y × G ↦ (⟨f q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hχJ : ∀ y v, χ y (Complex.I • v) = J (f y) (χ y v)) :
    Continuous fun q : Y × G ↦
      TotalSpace.mk' G (f q.1) (J.complexFrame (χ q.1) (hχJ q.1) q.2) :=
  ((J.toContinuousComplexStructure.totalSpaceHomeomorph G).symm.continuous.comp hχ).congr
    fun q ↦ by
      rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_symm_apply,
        complexFrame_apply]

open Module in
/-- **Complex frames along maps from contractible spaces.** For an almost complex structure `J`
on `M` and a complex normed space `G` of half the real dimension of `M`, along a continuous map
`f` from a contractible paracompact R₁ space there are real-linear isomorphisms
`φ y : G ≃ T_(f y) M`, continuous into the tangent bundle, carrying multiplication by `i` to `J`:
frames of the complex vector bundle `(TM, J)` along `f`. -/
theorem exists_continuous_frame (J : ContMDiffAlmostComplexStructure I n M)
    [Fact (finrank ℝ E = 2 * finrank ℂ G)] [R1Space Y] [ParacompactSpace Y] [ContractibleSpace Y]
    (hf : Continuous f) :
    ∃ φ : ∀ y, G ≃L[ℝ] TangentSpace I (f y),
      Continuous (fun q : Y × G ↦ (⟨f q.1, φ q.1 q.2⟩ : TangentBundle I M)) ∧
      ∀ y v, φ y (Complex.I • v) = J (f y) (φ y v) := by
  have : CompleteSpace G := FiniteDimensional.completeSpace ℂ G
  -- A frame of the complex vector bundle `(TM, J)` along `f`, read as real frames of `TM`.
  set Jc := J.toContinuousComplexStructure
  obtain ⟨ψ, hψ⟩ := _root_.TauCeti.exists_continuous_frame (𝕜 := ℂ) (F := G) (E := Jc.Fiber) hf
  let φ : ∀ y, G ≃L[ℝ] TangentSpace I (f y) := fun y ↦
    ((ψ y).restrictScalars' ℝ).trans (Jc.fiberEquiv (f y))
  have hφ (y : Y) (v : G) : φ y v = Jc.fiberEquiv (f y) (ψ y v) := by
    simp only [φ, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_restrictScalars']
  refine ⟨φ, ((Jc.totalSpaceHomeomorph G).continuous.comp hψ).congr fun q ↦ ?_, fun y v ↦ ?_⟩
  · simp only [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply,
      hφ]
  · rw [hφ, hφ, map_smul, Bundle.ContinuousComplexStructure.fiberEquiv_I_smul]
    exact J.toContinuousComplexStructure_apply (f y) _

end Frame

end TauCeti.ContMDiffAlmostComplexStructure

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] {Y : Type*}
  [TopologicalSpace Y] {f : Y → M}

/-- **The change between complex frames.** Two continuous frames of the tangent bundle along a map
`f`, with a complex model `G` and both complex linear for an almost complex structure `J`, differ by
a continuous family `k` of complex automorphisms of `G`, `φ y = φ' y ∘ k y`. -/
theorem exists_continuous_complex_frame_change (J : SmoothAlmostComplexStructure I M)
    {φ φ' : ∀ y, G ≃L[ℝ] TangentSpace I (f y)}
    (hφ : Continuous fun q : Y × G ↦ (⟨f q.1, φ q.1 q.2⟩ : TangentBundle I M))
    (hφ' : Continuous fun q : Y × G ↦ (⟨f q.1, φ' q.1 q.2⟩ : TangentBundle I M))
    (hφJ : ∀ y v, φ y (Complex.I • v) = J (f y) (φ y v))
    (hφJ' : ∀ y v, φ' y (Complex.I • v) = J (f y) (φ' y v)) :
    ∃ k : Y → G ≃L[ℂ] G, Continuous (fun y ↦ (k y : G →L[ℂ] G)) ∧
      ∀ y v, φ y v = φ' y (k y v) := by
  let k : Y → G ≃L[ℂ] G := fun y ↦
    ((φ y).trans (φ' y).symm).complexOfMapISmul (trans_symm_I_smul (hφJ y) (hφJ' y))
  have hk_apply (y : Y) (v : G) : k y v = (φ' y).symm (φ y v) :=
    ContinuousLinearEquiv.complexOfMapISmul_apply _ _ v
  refine ⟨k, (ContinuousLinearMap.restrictScalarsIsometry ℂ G G ℝ ℝ).isometry.isUniformInducing
    |>.isInducing.continuous_iff.2 ((continuous_trans_symm_of_continuous_frame hφ hφ').congr
      fun y ↦ ContinuousLinearMap.ext fun v ↦ (hk_apply y v).symm), fun y v ↦ ?_⟩
  rw [hk_apply, ContinuousLinearEquiv.apply_symm_apply]

end TauCeti.SmoothAlmostComplexStructure
