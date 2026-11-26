/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.ConleyZehnder.FrameChange
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic
import TauCeti.Geometry.Symplectic.ConleyZehnder.Parity
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.UnitaryFrame
import TauCeti.Geometry.Symplectic.WittExtension
import TauCeti.Topology.VectorBundle.Contractible

/-!
# The Conley–Zehnder index of a path along a capped loop

Let `σ` be a smooth two-form on a manifold `M`, such as a symplectic form, and `(W, ω₀)` a
finite-dimensional symplectic vector space. A **symplectic frame** of the tangent bundle along a map
`f : Y → M` (`TauCeti.SmoothTwoForm.IsSymplecticFrame`) is a family of linear isomorphisms
`φ y : W ≃ T_(f y) M`, continuous into the tangent bundle, carrying `ω₀` to `σ`.

Let `γ : [0, 1] → M` be a path and `Φ(t) : T_(γ 0) M ≃ T_(γ t) M` a continuous family of linear
isomorphisms preserving `σ`, such as the linearized flow `dφ_t(γ 0)` of a Hamiltonian along an
orbit. Read in a symplectic frame `χ` along `γ`, it becomes the path
`t ↦ χ(t)⁻¹ ∘ Φ(t) ∘ χ(0)` of linear symplectic maps of `W`
(`TauCeti.SmoothTwoForm.framePath`), whose Conley–Zehnder index is
`TauCeti.SmoothTwoForm.frameConleyZehnderIndex`.

* **Change of frame.** Two symplectic frames `χ`, `χ'` along `γ` differ by the path
  `t ↦ χ(t)⁻¹ ∘ χ'(t)` of linear symplectic maps of `W`. When it is a loop, for instance when
  `γ` is a loop and both frames are periodic, the index read in `χ'` is the index read in `χ` plus
  twice the Maslov index of this loop
  (`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_add_maslovIndex`).
* **Frames over a cap.** Let `f : Y → M` be a continuous map from a contractible space, for
  instance a disc bounding the loop `γ = f ∘ β` for a loop `β` in `Y`. Restricted along `β`, any
  two symplectic frames along `f` give the same index
  (`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_comp_eq`), even for different models `W`: the
  change of frame `y ↦ φ(y)⁻¹ ∘ φ'(y)` is defined on all of `Y`, so its loop along `β` has Maslov
  index zero. So the Conley–Zehnder index of `Φ` along the capped loop depends only on the cap
  `f`, not on the trivialization over it.
* **Existence.** When `σ` is nondegenerate and `M` is Hausdorff and σ-compact, there is a
  symplectic frame with any model of the right dimension along every continuous map from a
  contractible paracompact R₁ space
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_isSymplecticFrame`):
  a unitary frame for a compatible almost complex structure
  (`TauCeti.SmoothTwoForm.Compatible.exists_continuous_unitary_frame`), composed with a linear
  symplectomorphism of models.

In capped Hamiltonian Floer theory `γ` is a contractible periodic orbit, `f` a cap of it and `Φ`
the linearized flow along `γ`; the index read in a frame over the cap is then the Conley–Zehnder
index of the capped orbit, which grades the generators of the capped Floer complex.

## Main definitions

* `TauCeti.SmoothTwoForm.IsSymplecticFrame`: a symplectic frame of the tangent bundle along a map.
* `TauCeti.SmoothTwoForm.framePath`: a path of linear isomorphisms along `γ`, read in a frame.
* `TauCeti.SmoothTwoForm.frameConleyZehnderIndex`: its Conley–Zehnder index in a symplectic frame.

## Main results

* `TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_add_maslovIndex`: the change of frame law.
* `TauCeti.SmoothTwoForm.frameConleyZehnderIndex_comp_eq`: independence of the frame over a cap.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_isSymplecticFrame`: existence of symplectic frames.
* `TauCeti.SmoothTwoForm.exists_int_frameConleyZehnderIndex_eq`: in a periodic frame, the index
  of a family from the identity whose endpoint fixes no nonzero vector is an integer.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the Conley–Zehnder index of a capped periodic orbit, in
  a trivialization extending over the cap).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 12.1 (the Conley–Zehnder grading of capped periodic orbits).
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
  {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W']
  [NormedSpace ℝ W'] {ω₀ : SymplecticForm W} {ω' : SymplecticForm W'}
  {Y : Type*} [TopologicalSpace Y] {f : Y → M}

/-! ### Symplectic frames -/

variable (σ ω₀) in
/-- A **symplectic frame** of the tangent bundle along `f : Y → M`, with model a symplectic vector
space `(W, ω₀)`: linear isomorphisms `φ y : W ≃ T_(f y) M`, continuous into the tangent bundle,
carrying `ω₀` to the two-form `σ`. -/
structure IsSymplecticFrame (f : Y → M) (φ : ∀ y, W ≃L[ℝ] TangentSpace I (f y)) : Prop where
  /-- A symplectic frame is continuous into the tangent bundle. -/
  continuous : Continuous fun q : Y × W ↦ (⟨f q.1, φ q.1 q.2⟩ : TangentBundle I M)
  /-- A symplectic frame carries `ω₀` to `σ`. -/
  apply_apply (y : Y) (v w : W) : σ.eval₂ (f y) (φ y v) (φ y w) = ω₀ v w

namespace IsSymplecticFrame

variable {φ ψ : ∀ y, W ≃L[ℝ] TangentSpace I (f y)}

/-- A symplectic frame along `f` restricts to a symplectic frame along `f ∘ g`. -/
theorem comp (hφ : IsSymplecticFrame σ ω₀ f φ) {Z : Type*} [TopologicalSpace Z] {g : Z → Y}
    (hg : Continuous g) : IsSymplecticFrame σ ω₀ (f ∘ g) fun z ↦ φ (g z) :=
  ⟨hφ.continuous.comp ((hg.comp continuous_fst).prodMk continuous_snd),
    fun z ↦ hφ.apply_apply (g z)⟩

/-- A symplectic frame precomposed with a linear symplectomorphism of models `e : W' ≃ W` is a
symplectic frame with model `W'`. -/
theorem trans (hφ : IsSymplecticFrame σ ω₀ f φ) (e : W' ≃L[ℝ] W)
    (he : ∀ v w, ω₀ (e v) (e w) = ω' v w) : IsSymplecticFrame σ ω' f fun y ↦ e.trans (φ y) :=
  ⟨hφ.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)), fun y v w ↦ by
    simp only [ContinuousLinearEquiv.trans_apply, hφ.apply_apply, he]⟩

/-- Two symplectic frames along the same map differ by linear symplectic maps of the model:
`ψ(y)⁻¹ ∘ φ(y)` preserves `ω₀`. -/
theorem apply_trans_symm_apply (hφ : IsSymplecticFrame σ ω₀ f φ)
    (hψ : IsSymplecticFrame σ ω₀ f ψ) (y : Y) (v w : W) :
    ω₀ ((φ y).trans (ψ y).symm v) ((φ y).trans (ψ y).symm w) = ω₀ v w := by
  rw [← hψ.apply_apply y, ← hφ.apply_apply y]
  simp

end IsSymplecticFrame

variable [FiniteDimensional ℝ E]

/-- **Existence of symplectic frames.** Let `σ` be a fiberwise nondegenerate smooth two-form on a
Hausdorff σ-compact manifold, and `(W, ω₀)` a symplectic vector space of the dimension of `M`.
Along every continuous map `f` from a contractible paracompact R₁ space there is a symplectic
frame of the tangent bundle with model `(W, ω₀)`. -/
theorem IsNondegenerate.exists_isSymplecticFrame [T2Space M] [SigmaCompactSpace M]
    [FiniteDimensional ℝ W] [R1Space Y] [ParacompactSpace Y] [ContractibleSpace Y]
    (h : σ.IsNondegenerate) (hW : finrank ℝ W = finrank ℝ E) (hf : Continuous f) :
    ∃ φ, IsSymplecticFrame σ ω₀ f φ := by
  -- A unitary frame with model `ℂⁿ`, `2 n = dim M`, for a compatible almost complex structure.
  let G := EuclideanSpace ℂ (Fin (finrank ℝ E / 2))
  have hG : finrank ℝ G = finrank ℝ E := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin, Nat.two_mul_div_two_of_even]
    exact hW ▸ ω₀.even_finrank
  have : Fact (finrank ℝ E = 2 * finrank ℂ G) := ⟨hG.symm.trans (finrank_real_of_complex G)⟩
  obtain ⟨J, hJ⟩ := h.exists_compatible
  obtain ⟨φ, hφc, -, -, hφ⟩ := hJ.exists_continuous_unitary_frame (G := G) hf
  -- A linear symplectomorphism `(W, ω₀) ≃ (G, Im ⟪·, ·⟫)` moves the model to `W`.
  obtain ⟨e, he⟩ := SymplecticForm.exists_isSymplectomorphism ω₀ (imInnerSymplecticForm G)
    (hW.trans hG.symm)
  refine ⟨fun y ↦ (e.toContinuousLinearEquiv).trans (φ y),
    (IsSymplecticFrame.trans
      (⟨hφc, fun y v w ↦ ?_⟩ : IsSymplecticFrame σ (imInnerSymplecticForm G) f φ)
      e.toContinuousLinearEquiv fun v w ↦ ?_)⟩
  · rw [hφ, imInnerSymplecticForm_apply]
  · exact he.apply v w

/-! ### The Conley–Zehnder index in a symplectic frame -/

variable {γ : unitInterval → M} {χ χ' : ∀ t, W ≃L[ℝ] TangentSpace I (γ t)}
  {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}

/-- **A path read in a frame.** For a frame `χ` along a path `γ` and a continuous family of linear
isomorphisms `Φ(t) : T_(γ 0) M ≃ T_(γ t) M`, the path `t ↦ χ(t)⁻¹ ∘ Φ(t) ∘ χ(0)` of linear
automorphisms of the model `W`. -/
def framePath (hχ : Continuous fun q : unitInterval × W ↦
      (⟨γ q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M)) :
    Path ((((χ 0).trans (Φ 0)).trans (χ 0).symm : W ≃L[ℝ] W) : W →L[ℝ] W)
      ((((χ 0).trans (Φ 1)).trans (χ 1).symm : W ≃L[ℝ] W) : W →L[ℝ] W) where
  toFun t := (((χ 0).trans (Φ t)).trans (χ t).symm : W ≃L[ℝ] W)
  continuous_toFun :=
    continuous_trans_symm_of_continuous_frame (φ := fun t ↦ (χ 0).trans (Φ t))
      (hΦ.comp (continuous_fst.prodMk ((χ 0).continuous.comp continuous_snd))) hχ
  source' := rfl
  target' := rfl

/-- At time `t`, the path read in the frame `χ` is `χ(t)⁻¹ ∘ Φ(t) ∘ χ(0)`. -/
@[simp]
theorem framePath_apply (hχ : Continuous fun q : unitInterval × W ↦
      (⟨γ q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (t : unitInterval) (v : W) : framePath hχ hΦ t v = (χ t).symm (Φ t (χ 0 v)) :=
  (rfl)

/-- If `Φ` preserves `σ` and `χ` is a symplectic frame, the path read in `χ` runs through linear
symplectic maps of `(W, ω₀)`. -/
theorem apply_framePath_apply (hχ : IsSymplecticFrame σ ω₀ γ χ)
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) (t : unitInterval)
    (u v : W) :
    ω₀ (framePath hχ.continuous hΦ t u) (framePath hχ.continuous hΦ t v) = ω₀ u v := by
  rw [framePath_apply, framePath_apply, ← hχ.apply_apply t, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, hΦσ, hχ.apply_apply]

variable (ω₀) in
/-- **The Conley–Zehnder index in a symplectic frame.** The Conley–Zehnder index of the path
`t ↦ χ(t)⁻¹ ∘ Φ(t) ∘ χ(0)` of linear symplectic maps of `(W, ω₀)`, for a family `Φ` of linear
isomorphisms along `γ` preserving `σ`, read in a symplectic frame `χ` along `γ`. -/
def frameConleyZehnderIndex [FiniteDimensional ℝ W] (hχ : IsSymplecticFrame σ ω₀ γ χ)
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) : ℝ :=
  ω₀.conleyZehnderIndex (framePath hχ.continuous hΦ) (apply_framePath_apply hχ hΦ hΦσ)

/-- The Conley–Zehnder index in a frame is the Conley–Zehnder index of the path read in it. -/
theorem frameConleyZehnderIndex_def [FiniteDimensional ℝ W] (hχ : IsSymplecticFrame σ ω₀ γ χ)
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex ω₀ hχ hΦ hΦσ =
      ω₀.conleyZehnderIndex (framePath hχ.continuous hΦ) (apply_framePath_apply hχ hΦ hΦσ) :=
  (rfl)

/-- **Change of model.** Precomposing a symplectic frame with a linear symplectomorphism of
models `e : W' ≃ W` does not change the Conley–Zehnder index read in it. -/
theorem frameConleyZehnderIndex_trans [FiniteDimensional ℝ W] [FiniteDimensional ℝ W']
    (hχ : IsSymplecticFrame σ ω₀ γ χ) (e : W' ≃L[ℝ] W) (he : ∀ v w, ω₀ (e v) (e w) = ω' v w)
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex ω' (hχ.trans e he) hΦ hΦσ = frameConleyZehnderIndex ω₀ hχ hΦ hΦσ := by
  -- Read in `e⁻¹ ∘ χ`, the path is the conjugate `e⁻¹ ∘ Ψ ∘ e` of the path `Ψ` read in `χ`.
  have he' : SymplecticForm.IsSymplectomorphism ω₀ ω' e.symm.toLinearEquiv :=
    SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ by
      simpa using (he (e.symm v) (e.symm w)).symm
  rw [frameConleyZehnderIndex_def, frameConleyZehnderIndex_def,
    ← SymplecticForm.conleyZehnderIndex_map_conj ω₀ e.symm he']
  exact ω'.conleyZehnderIndex_congr _ _ _ fun t ↦ by
    ext v
    rw [Path.map_coe, Function.comp_apply]
    simp

/-- **The index of a nondegenerate return map is an integer.** Let `χ` be a symplectic frame along
`γ` taking the same values at the two ends, for instance a periodic frame along a loop, and let `Φ`
be a family of linear maps along `γ` preserving `σ` which starts at the identity and whose endpoint
`Φ(1)` fixes no nonzero vector, as the linearized flow along a nondegenerate periodic orbit does.
Then the Conley–Zehnder index of `Φ` read in `χ` is an integer. -/
theorem exists_int_frameConleyZehnderIndex_eq [FiniteDimensional ℝ W]
    (hχ : IsSymplecticFrame σ ω₀ γ χ) (hχ₁ : ∀ v, χ 0 v = χ 1 v)
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) (hΦ₀ : ∀ v, Φ 0 v = v)
    (hΦ₁ : ∀ v, Φ 1 v = v → v = 0) :
    ∃ k : ℤ, frameConleyZehnderIndex ω₀ hχ hΦ hΦσ = k := by
  -- Read in `χ`, the path starts at the identity of the model.
  have hA : (1 : W →L[ℝ] W) = (((χ 0).trans (Φ 0)).trans (χ 0).symm : W ≃L[ℝ] W) := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    -- Unfold the composite pointwise: its middle factor `Φ 0` maps `T_(γ 0) M` to itself only
    -- up to the definitional equality of tangent spaces, which `simp` lemmas cannot match.
    change v = (χ 0).symm (Φ 0 (χ 0 v))
    rw [hΦ₀, ContinuousLinearEquiv.symm_apply_apply]
  -- and its endpoint `χ(1)⁻¹ ∘ Φ(1) ∘ χ(0)` fixes no nonzero vector of the model.
  have hB : End.eigenspace (((((χ 0).trans (Φ 1)).trans (χ 1).symm : W ≃L[ℝ] W) : W →L[ℝ] W) :
      W →ₗ[ℝ] W) 1 = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv ↦ ?_
    rw [End.mem_eigenspace_iff, one_smul] at hv
    -- The same unfolding of the composite, applied to `v`.
    have hv' : (χ 1).symm (Φ 1 (χ 0 v)) = v := hv
    exact (χ 0).map_eq_zero_iff.1 (hΦ₁ _ (((χ 1).symm_apply_eq.1 hv').trans (hχ₁ v).symm))
  obtain ⟨k, hk, -⟩ := ω₀.exists_int_conleyZehnderIndex_eq_of_one
    ((framePath hχ.continuous hΦ).cast hA rfl) (apply_framePath_apply hχ hΦ hΦσ) hB
  exact ⟨k, (ω₀.conleyZehnderIndex_congr (framePath hχ.continuous hΦ)
    ((framePath hχ.continuous hΦ).cast hA rfl) _ fun _ ↦ rfl).trans hk⟩

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- The change of frame `t ↦ χ(t)⁻¹ ∘ χ'(t)` between two frames along `γ` takes the same value at
the two ends when both frames do: this is the loop condition of
`TauCeti.SmoothTwoForm.transitionLoop`. -/
theorem trans_symm_zero_eq_trans_symm_one (h : ∀ v, χ 0 v = χ 1 v) (h' : ∀ v, χ' 0 v = χ' 1 v) :
    (χ' 0).trans (χ 0).symm = (χ' 1).trans (χ 1).symm := by
  ext v
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, h']
  apply (χ 0).injective
  -- `χ 0` and `χ 1` take values in the tangent spaces at `γ 0` and `γ 1`, equal only
  -- definitionally, so the inverses are cancelled by explicit terms rather than `rw`.
  exact ((χ 0).apply_symm_apply _).trans ((h _).trans ((χ 1).apply_symm_apply _)).symm

/-- The change of frame from `χ` to `χ'` along `γ`, the path `t ↦ χ(t)⁻¹ ∘ χ'(t)` of linear
automorphisms of the model, as a loop when it is one (`hper`). -/
def transitionLoop (hχ : Continuous fun q : unitInterval × W ↦
      (⟨γ q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hχ' : Continuous fun q : unitInterval × W ↦
      (⟨γ q.1, χ' q.1 q.2⟩ : TangentBundle I M))
    (hper : (χ' 0).trans (χ 0).symm = (χ' 1).trans (χ 1).symm) :
    Path (((χ' 0).trans (χ 0).symm : W ≃L[ℝ] W) : W →L[ℝ] W)
      (((χ' 0).trans (χ 0).symm : W ≃L[ℝ] W) : W →L[ℝ] W) where
  toFun t := ((χ' t).trans (χ t).symm : W ≃L[ℝ] W)
  continuous_toFun := continuous_trans_symm_of_continuous_frame hχ' hχ
  source' := rfl
  target' := by rw [hper]

/-- At time `t` the change of frame from `χ` to `χ'` is `χ(t)⁻¹ ∘ χ'(t)`. -/
@[simp]
theorem transitionLoop_apply
    (hχ : Continuous fun q : unitInterval × W ↦
      (⟨γ q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hχ' : Continuous fun q : unitInterval × W ↦
      (⟨γ q.1, χ' q.1 q.2⟩ : TangentBundle I M))
    (hper : (χ' 0).trans (χ 0).symm = (χ' 1).trans (χ 1).symm) (t : unitInterval) (v : W) :
    transitionLoop hχ hχ' hper t v = (χ t).symm (χ' t v) :=
  (rfl)

/-- The change of frame between two symplectic frames runs through linear symplectic maps of the
model. -/
theorem apply_transitionLoop_apply (hχ : IsSymplecticFrame σ ω₀ γ χ)
    (hχ' : IsSymplecticFrame σ ω₀ γ χ')
    (hper : (χ' 0).trans (χ 0).symm = (χ' 1).trans (χ 1).symm) (t : unitInterval) (u v : W) :
    ω₀ (transitionLoop hχ.continuous hχ'.continuous hper t u)
      (transitionLoop hχ.continuous hχ'.continuous hper t v) = ω₀ u v := by
  simpa using hχ'.apply_trans_symm_apply hχ t u v

/-- **Change of frame.** Let `χ` and `χ'` be symplectic frames along `γ` whose change of frame
`t ↦ χ(t)⁻¹ ∘ χ'(t)` is a loop, for instance periodic frames along a loop. Then the
Conley–Zehnder index of `Φ` read in `χ'` is its index read in `χ` plus twice the Maslov index of
the change of frame. -/
theorem frameConleyZehnderIndex_eq_add_maslovIndex [FiniteDimensional ℝ W]
    (hχ : IsSymplecticFrame σ ω₀ γ χ) (hχ' : IsSymplecticFrame σ ω₀ γ χ')
    (hper : (χ' 0).trans (χ 0).symm = (χ' 1).trans (χ 1).symm)
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex ω₀ hχ' hΦ hΦσ = frameConleyZehnderIndex ω₀ hχ hΦ hΦσ +
      2 * ω₀.maslovIndex (transitionLoop hχ.continuous hχ'.continuous hper)
        (apply_transitionLoop_apply hχ hχ' hper) := by
  -- The inverse change of frame `t ↦ χ'(t)⁻¹ ∘ χ(t)` is a loop as well.
  have hper' : (χ 0).trans (χ' 0).symm = (χ 1).trans (χ' 1).symm := by
    ext v
    simpa using congrArg (fun e : W ≃L[ℝ] W ↦ e.symm v) hper
  -- Read in `χ'`, the path is `g(t)⁻¹ Ψ(t) g(0)` for the path `Ψ` read in `χ`.
  rw [frameConleyZehnderIndex_def, frameConleyZehnderIndex_def]
  refine Eq.trans ?_ (ω₀.conleyZehnderIndex_frameChange
    (transitionLoop hχ.continuous hχ'.continuous hper) (apply_transitionLoop_apply hχ hχ' hper)
    (transitionLoop hχ'.continuous hχ.continuous hper') (fun t u ↦ by simp) _ _)
  exact ω₀.conleyZehnderIndex_congr _ _ _ fun t ↦ by
    ext v
    rw [SymplecticForm.frameChange_apply]
    simp

/-- **The Conley–Zehnder index over a cap does not depend on the frame.** Let `f : Y → M` be a
continuous map from a contractible space, `β` a loop in `Y`, and `Φ` a family of linear
isomorphisms preserving `σ` along the loop `f ∘ β`. Restricted along `β`, any two symplectic frames
along `f`, with any two models, give the same Conley–Zehnder index of `Φ`. -/
theorem frameConleyZehnderIndex_comp_eq [FiniteDimensional ℝ W] [FiniteDimensional ℝ W']
    [ContractibleSpace Y] {φ : ∀ y, W ≃L[ℝ] TangentSpace I (f y)}
    {φ' : ∀ y, W' ≃L[ℝ] TangentSpace I (f y)} (hφ : IsSymplecticFrame σ ω₀ f φ)
    (hφ' : IsSymplecticFrame σ ω' f φ') {y₀ : Y} (β : Path y₀ y₀)
    {Φ : ∀ t, TangentSpace I (f (β 0)) ≃L[ℝ] TangentSpace I (f (β t))}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (f (β 0)) ↦
      (⟨f (β q.1), Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (f (β t)) (Φ t u) (Φ t v) = σ.eval₂ (f (β 0)) u v) :
    frameConleyZehnderIndex ω' (hφ'.comp β.continuous) hΦ hΦσ =
      frameConleyZehnderIndex ω₀ (hφ.comp β.continuous) hΦ hΦσ := by
  -- Move the model of `φ'` to `(W, ω₀)` by a linear symplectomorphism `e : W ≃ W'`.
  have hdim : finrank ℝ W = finrank ℝ W' :=
    ((φ y₀).toLinearEquiv.finrank_eq).trans (φ' y₀).toLinearEquiv.finrank_eq.symm
  obtain ⟨e, he⟩ := SymplecticForm.exists_isSymplectomorphism ω₀ ω' hdim
  have he' : ∀ v w, ω' (e.toContinuousLinearEquiv v) (e.toContinuousLinearEquiv w) = ω₀ v w :=
    he.apply
  have hφ'' := hφ'.trans e.toContinuousLinearEquiv he'
  rw [← frameConleyZehnderIndex_trans (hφ'.comp β.continuous) e.toContinuousLinearEquiv he']
  -- Both frames are now frames with model `W`; their change of frame is defined on all of `Y`.
  rw [frameConleyZehnderIndex_eq_add_maslovIndex (hφ.comp β.continuous) (hφ''.comp β.continuous)
    (congrArg (fun y ↦ (e.toContinuousLinearEquiv.trans (φ' y)).trans (φ y).symm)
      (β.source.trans β.target.symm))]
  have ha := continuous_trans_symm_of_continuous_frame
    (φ := fun y ↦ e.toContinuousLinearEquiv.trans (φ' y)) (ψ := φ) hφ''.continuous hφ.continuous
  rw [ω₀.maslovIndex_congr _ (β.map ha) _ fun t ↦ by ext v; simp,
    ω₀.maslovIndex_map_eq_zero ha (hφ''.apply_trans_symm_apply hφ), Int.cast_zero, mul_zero,
    add_zero]

end TauCeti.SmoothTwoForm
