/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Chart
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import TauCeti.Analysis.Fredholm.Stabilization

/-!
# The determinant line bundle of a continuous Fredholm family

Let `T : X → (E →L[𝕜] F)` be a continuous family of Fredholm operators between Banach spaces. The
determinant lines `det (ker (T x)) ⊗ (det (F ⧸ range (T x)))^*` form a line bundle over `X`,
although the kernel and the cokernel of `T x` jump in dimension. This is the line bundle whose
orientations orient the moduli spaces of Morse and Floer theory, through the linearized operators.

The fibres are the type synonym `TauCeti.DetLineBundle T`, which gives each determinant line its
module topology. The local trivializations are the kernel charts of
`TauCeti.Analysis.Fredholm.DeterminantLine.Chart`: a finite stabilization `D₂ : Λ →L[𝕜] F` with a
kernel coordinate `q : E × Λ →L[𝕜] G` identifies the determinant line of `T x` with the fixed
line `det G ⊗ (det Λ)^*` wherever the pair `((T x).coprod D₂).prod q` is invertible, an open set
of parameters (`TauCeti.detLineChartSet`). Read through an isomorphism of that line with `𝕜`,
this is a pretrivialization with model fibre `𝕜` (`TauCeti.detLinePretrivialization`), and the
transitions between two such charts are continuous
(`TauCeti.continuousOn_detLinePretrivialization_coordChange`), because their scalar factors are
(`ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`). Kernel charts exist
near every Fredholm operator
(`ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates`), so they assemble
into a vector prebundle, `TauCeti.detLineVectorPrebundle`. Mathlib then supplies the topology of
the total space (`VectorPrebundle.totalSpaceTopology`), for which the determinant lines form a
fibre bundle (`VectorPrebundle.toFiberBundle`) and a topological vector bundle of rank one
(`VectorPrebundle.toVectorBundle`, with `TauCeti.DetLineBundle.finrank_eq_one`), and in which
the kernel charts whose stabilizer is a finite-dimensional subspace of `F` are trivializations
(`TauCeti.detLinePretrivialization_mem_pretrivializationAtlas`).

## Main definitions

* `TauCeti.DetLineBundle`: the determinant lines of a family of operators, as a family of
  topological vector spaces over the parameter space.
* `TauCeti.detLinePretrivialization`: a kernel chart as a pretrivialization with model fibre `𝕜`.
* `TauCeti.detLineVectorPrebundle`: the determinant line bundle of a continuous Fredholm family.

## Main results

* `TauCeti.continuousOn_detLinePretrivialization_coordChange`: the transitions between kernel
  charts are continuous.
* `TauCeti.detLinePretrivialization_mem_pretrivializationAtlas`: the kernel charts with a
  finite-dimensional subspace of the target as stabilizer are trivializations of the bundle.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Bundle Module Set Topology TensorProduct

namespace TauCeti

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (T : X → E →L[𝕜] F) in
/-- The determinant lines of a family of operators `T x : E →L[𝕜] F`, as a family of types over
the parameter space: the fibre at `x` is `det (ker (T x)) ⊗ (det (F ⧸ range (T x)))^*`. It is a
type synonym so that it can carry the module topology; `TauCeti.DetLineBundle.linearEquiv`
identifies it with the determinant line of `T x`. -/
def DetLineBundle (x : X) : Type _ := ((T x : E →L[𝕜] F) : E →ₗ[𝕜] F).detLine

namespace DetLineBundle

variable {T : X → E →L[𝕜] F}

noncomputable instance (x : X) : AddCommGroup (DetLineBundle T x) :=
  inferInstanceAs (AddCommGroup ((T x : E →ₗ[𝕜] F).detLine))

noncomputable instance (x : X) : Module 𝕜 (DetLineBundle T x) :=
  inferInstanceAs (Module 𝕜 ((T x : E →ₗ[𝕜] F).detLine))

/-- The fibres of the determinant line bundle carry the module topology. On the
finite-dimensional fibres of a Fredholm family this is the unique Hausdorff vector-space
topology. -/
noncomputable instance (x : X) : TopologicalSpace (DetLineBundle T x) := moduleTopology 𝕜 _

instance (x : X) : IsModuleTopology 𝕜 (DetLineBundle T x) := ⟨rfl⟩

instance (x : X) : ContinuousAdd (DetLineBundle T x) := IsModuleTopology.toContinuousAdd 𝕜 _

variable (T) in
/-- The fibre of `DetLineBundle T` at `x` is the determinant line of `T x`. -/
noncomputable def linearEquiv (x : X) :
    DetLineBundle T x ≃ₗ[𝕜] ((T x : E →L[𝕜] F) : E →ₗ[𝕜] F).detLine :=
  LinearEquiv.refl 𝕜 _

/-- The fibres of the determinant line bundle of a Fredholm family are lines. -/
theorem finrank_eq_one {x : X} (hT : (T x).IsFredholm) : finrank 𝕜 (DetLineBundle T x) = 1 :=
  (linearEquiv T x).finrank_eq.trans hT.finrank_detLine

end DetLineBundle

section Chart

variable {Λ G Λ₃ G₃ : Type*} [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup Λ₃] [NormedSpace 𝕜 Λ₃]
  [NormedAddCommGroup G₃] [NormedSpace 𝕜 G₃] {T : X → E →L[𝕜] F}

variable (T) in
/-- The parameters at which the stabilization of `T x` by `D₂`, paired with the kernel coordinate
`q`, is invertible: the domain of the kernel chart `ContinuousLinearMap.detLineChartEquiv`. -/
def detLineChartSet (D₂ : Λ →L[𝕜] F) (q : E × Λ →L[𝕜] G) : Set X :=
  {x | (((T x).coprod D₂).prod q).IsInvertible}

@[simp]
theorem mem_detLineChartSet {D₂ : Λ →L[𝕜] F} {q : E × Λ →L[𝕜] G} {x : X} :
    x ∈ detLineChartSet T D₂ q ↔ (((T x).coprod D₂).prod q).IsInvertible :=
  Iff.rfl

variable [TopologicalSpace X]

/-- The domain of a kernel chart of a continuous family is open. -/
theorem isOpen_detLineChartSet [CompleteSpace E] [CompleteSpace Λ] (hT : Continuous T)
    (D₂ : Λ →L[𝕜] F) (q : E × Λ →L[𝕜] G) : IsOpen (detLineChartSet T D₂ q) := by
  have hc : Continuous fun x ↦ ((T x).coprod D₂).prod q :=
    (ContinuousLinearMap.prodL 𝕜).continuous.comp
      ((hT.continuousLinearMapCoprod (continuous_const (y := D₂))).prodMk
        (continuous_const (y := q)))
  exact ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hc

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G]
  [FiniteDimensional 𝕜 Λ₃] [FiniteDimensional 𝕜 G₃] [CompleteSpace E]

open scoped Classical in
/-- **The kernel chart as a pretrivialization.** Over the open set `detLineChartSet T D₂ q`, the
kernel chart `ContinuousLinearMap.detLineChartEquiv` identifies the determinant line of `T x` with
the fixed line `det G ⊗ (det Λ)^*`; reading this line through `b` trivializes the determinant
lines of the family over that set, with model fibre `𝕜`. -/
noncomputable def detLinePretrivialization (hT : Continuous T) (D₂ : Λ →L[𝕜] F)
    (q : E × Λ →L[𝕜] G) (b : detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (detLine 𝕜 Λ) ≃ₗ[𝕜] 𝕜) :
    Pretrivialization 𝕜 (π 𝕜 (DetLineBundle T)) where
  toFun z := (z.proj, if h : z.proj ∈ detLineChartSet T D₂ q then
    b (ContinuousLinearMap.detLineChartEquiv (T z.proj) D₂ q h
      (DetLineBundle.linearEquiv T z.proj z.2)) else 0)
  invFun p := ⟨p.1, if h : p.1 ∈ detLineChartSet T D₂ q then
    (DetLineBundle.linearEquiv T p.1).symm
      ((ContinuousLinearMap.detLineChartEquiv (T p.1) D₂ q h).symm (b.symm p.2)) else 0⟩
  source := π 𝕜 (DetLineBundle T) ⁻¹' detLineChartSet T D₂ q
  target := detLineChartSet T D₂ q ×ˢ univ
  map_source' _ hz := ⟨hz, mem_univ _⟩
  map_target' _ hp := hp.1
  left_inv' := by
    rintro ⟨x, v⟩ hx
    have hx' : x ∈ detLineChartSet T D₂ q := mem_preimage.1 hx
    simp only [hx', ↓reduceDIte, LinearEquiv.symm_apply_apply]
  right_inv' := by
    rintro ⟨x, w⟩ ⟨hx, -⟩
    simp [hx]
  open_target :=
    have := FiniteDimensional.complete 𝕜 Λ
    (isOpen_detLineChartSet hT D₂ q).prod isOpen_univ
  baseSet := detLineChartSet T D₂ q
  open_baseSet :=
    have := FiniteDimensional.complete 𝕜 Λ
    isOpen_detLineChartSet hT D₂ q
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable (hT : Continuous T) (D₂ : Λ →L[𝕜] F) (q : E × Λ →L[𝕜] G)
  (b : detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (detLine 𝕜 Λ) ≃ₗ[𝕜] 𝕜)

/-- The domain of a kernel chart is the set of parameters where its pair is invertible. -/
@[simp]
theorem detLinePretrivialization_baseSet :
    (detLinePretrivialization hT D₂ q b).baseSet = detLineChartSet T D₂ q :=
  (rfl)

/-- On its domain, a kernel chart is the kernel chart of the determinant line of `T x` read
through `b`. -/
@[simp]
theorem detLinePretrivialization_apply_mk {x : X} (hx : x ∈ detLineChartSet T D₂ q)
    (v : DetLineBundle T x) :
    detLinePretrivialization hT D₂ q b ⟨x, v⟩ =
      (x, b (ContinuousLinearMap.detLineChartEquiv (T x) D₂ q (mem_detLineChartSet.1 hx)
        (DetLineBundle.linearEquiv T x v))) := by
  -- `simp` does not unfold the coercion of the structure to a function, so state the value of
  -- its `toFun` field directly.
  change (x, _) = _
  simp only [hx, ↓reduceDIte]

/-- On its domain, the inverse of a kernel chart is the inverse of the kernel chart of the
determinant line of `T x`, after `b⁻¹`. -/
@[simp]
theorem detLinePretrivialization_symm_apply {x : X} (hx : x ∈ detLineChartSet T D₂ q) (w : 𝕜) :
    (detLinePretrivialization hT D₂ q b).symm x w =
      (DetLineBundle.linearEquiv T x).symm
        ((ContinuousLinearMap.detLineChartEquiv (T x) D₂ q (mem_detLineChartSet.1 hx)).symm
          (b.symm w)) := by
  have h := congrArg Prod.snd ((detLinePretrivialization hT D₂ q b).apply_mk_symm hx w)
  rw [detLinePretrivialization_apply_mk hT D₂ q b hx] at h
  rw [eq_comm, LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq]
  exact h.symm

/-- Kernel charts are linear on each fibre. -/
instance isLinear_detLinePretrivialization :
    (detLinePretrivialization hT D₂ q b).IsLinear 𝕜 where
  linear x hx := by
    have : (fun v : DetLineBundle T x ↦ (detLinePretrivialization hT D₂ q b ⟨x, v⟩).2) =
        ((DetLineBundle.linearEquiv T x).trans
          ((ContinuousLinearMap.detLineChartEquiv (T x) D₂ q (mem_detLineChartSet.1 hx)).trans b) :
            _ →ₗ[𝕜] 𝕜) := by
      ext v
      simp [detLinePretrivialization_apply_mk hT D₂ q b hx]
    rw [this]
    exact LinearMap.isLinear _

/-- The fibre of a kernel chart over a point of its domain is a homeomorphism onto `𝕜`, so the
chart induces the topology of each fibre. -/
theorem isInducing_detLinePretrivialization_comp_mk {x : X} (hx : x ∈ detLineChartSet T D₂ q) :
    IsInducing (detLinePretrivialization hT D₂ q b ∘ TotalSpace.mk x) := by
  let L := (DetLineBundle.linearEquiv T x).trans
    ((ContinuousLinearMap.detLineChartEquiv (T x) D₂ q (mem_detLineChartSet.1 hx)).trans b)
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L.toLinearMap
  have hLs : Continuous L.symm := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap
  have h : detLinePretrivialization hT D₂ q b ∘ TotalSpace.mk x = fun v ↦ (x, L v) :=
    funext fun v ↦ detLinePretrivialization_apply_mk hT D₂ q b hx v
  rw [h]
  exact IsInducing.of_comp (continuous_const.prodMk hL) continuous_snd
    (Homeomorph.mk L.toEquiv hL hLs).isInducing

/-- **The transitions between kernel charts are continuous.** For two kernel charts of a
continuous family, the coordinate change `𝕜 → 𝕜` from the first to the second, multiplication by
the image of `1`, depends continuously on the parameter where both charts are defined. -/
theorem continuousOn_detLinePretrivialization_coordChange (D₃ : Λ₃ →L[𝕜] F)
    (q₃ : E × Λ₃ →L[𝕜] G₃) (b₃ : detLine 𝕜 G₃ ⊗[𝕜] Dual 𝕜 (detLine 𝕜 Λ₃) ≃ₗ[𝕜] 𝕜) :
    ContinuousOn (fun x ↦ (detLinePretrivialization hT D₃ q₃ b₃
        ⟨x, (detLinePretrivialization hT D₂ q b).symm x 1⟩).2)
      (detLineChartSet T D₂ q ∩ detLineChartSet T D₃ q₃) := by
  set U := detLineChartSet T D₂ q ∩ detLineChartSet T D₃ q₃
  rw [continuousOn_iff_continuous_domRestrict]
  rcases isEmpty_or_nonempty U with hU | ⟨⟨x₀⟩⟩
  · exact continuous_of_discreteTopology
  -- On `U`, the transition is a continuous multiple of its value at `x₀`.
  obtain ⟨c, hc, -, hcx⟩ := ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul
    (T := fun x : U ↦ T x) (hT.comp continuous_subtype_val)
    (fun x ↦ mem_detLineChartSet.1 x.2.2) (fun x ↦ mem_detLineChartSet.1 x.2.1) x₀
  refine (hc.mul (continuous_const (y := b₃ (ContinuousLinearMap.detLineChartEquiv (T x₀) D₃ q₃
    (mem_detLineChartSet.1 x₀.2.2) ((ContinuousLinearMap.detLineChartEquiv (T x₀) D₂ q
      (mem_detLineChartSet.1 x₀.2.1)).symm (b.symm 1)))))).congr fun x ↦ ?_
  simp only [domRestrict_apply, detLinePretrivialization_symm_apply hT D₂ q b x.2.1,
    detLinePretrivialization_apply_mk hT D₃ q₃ b₃ x.2.2, LinearEquiv.apply_symm_apply, hcx x,
    map_smul, smul_eq_mul, Pi.mul_apply]

end Chart

section Bundle

variable [TopologicalSpace X] [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]
  {T : X → E →L[𝕜] F} (hT : Continuous T)

/-- The kernel charts whose stabilizer is the inclusion of a finite-dimensional subspace `S` of the
target and whose kernel coordinate takes values in a finite-dimensional subspace of `E × S`. -/
private noncomputable def detLineAtlas : Set (Pretrivialization 𝕜 (π 𝕜 (DetLineBundle T))) :=
  {e | ∃ (S : Submodule 𝕜 F) (_ : FiniteDimensional 𝕜 S) (G : Submodule 𝕜 (E × S))
    (_ : FiniteDimensional 𝕜 G) (q : E × S →L[𝕜] G)
    (b : detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (detLine 𝕜 S) ≃ₗ[𝕜] 𝕜),
    e = detLinePretrivialization hT S.subtypeL q b}

/-- Every point of a Fredholm family lies in the domain of a kernel chart of the atlas. -/
private theorem exists_mem_detLineAtlas (hF : ∀ x, (T x).IsFredholm) (x : X) :
    ∃ e ∈ detLineAtlas hT, x ∈ e.baseSet := by
  obtain ⟨S, -, -, hS, q, U, -, hxU, hinv⟩ :=
    (hF x).exists_stabilization_kernel_coordinates hT.continuousAt (D := ⊤) (by simp)
  have := ((hF x).coprod_of_finiteDimensional S.subtypeL).finite_ker
  have hx : x ∈ detLineChartSet T S.subtypeL q := hinv x hxU
  have h1 : finrank 𝕜 (detLine 𝕜 ((T x).coprod S.subtypeL).ker ⊗[𝕜] Dual 𝕜 (detLine 𝕜 S)) =
      finrank 𝕜 𝕜 := by
    rw [← (ContinuousLinearMap.detLineChartEquiv (T x) S.subtypeL q hx).finrank_eq,
      (hF x).finrank_detLine, finrank_self]
  have := Module.finite_of_finrank_eq_succ (n := 0) (h1.trans (finrank_self 𝕜))
  exact ⟨_, ⟨S, inferInstance, _, inferInstance, q, LinearEquiv.ofFinrankEq _ _ h1, rfl⟩, hx⟩

/-- **The determinant line bundle of a continuous Fredholm family.** The determinant lines
`DetLineBundle T` of a continuous family of Fredholm operators form a vector prebundle with model
fibre `𝕜`, whose pretrivializations are the kernel charts `detLinePretrivialization` with a
finite-dimensional subspace of the target as stabilizer. `VectorPrebundle.totalSpaceTopology`,
`VectorPrebundle.toFiberBundle` and `VectorPrebundle.toVectorBundle` then make it a topological
line bundle, in which each fibre has its module topology. -/
noncomputable def detLineVectorPrebundle (hF : ∀ x, (T x).IsFredholm) :
    VectorPrebundle 𝕜 𝕜 (DetLineBundle T) where
  pretrivializationAtlas := detLineAtlas hT
  pretrivialization_linear' := by
    rintro _ ⟨S, _, G, _, q, b, rfl⟩
    infer_instance
  pretrivializationAt x := (exists_mem_detLineAtlas hT hF x).choose
  mem_base_pretrivializationAt x := (exists_mem_detLineAtlas hT hF x).choose_spec.2
  pretrivialization_mem_atlas x := (exists_mem_detLineAtlas hT hF x).choose_spec.1
  exists_coordChange := by
    rintro _ ⟨S, _, G, _, q, b, rfl⟩ _ ⟨S', _, G', _, q', b', rfl⟩
    refine ⟨fun x ↦ (detLinePretrivialization hT S'.subtypeL q' b'
        ⟨x, (detLinePretrivialization hT S.subtypeL q b).symm x 1⟩).2 • ContinuousLinearMap.id 𝕜 𝕜,
      (continuousOn_detLinePretrivialization_coordChange hT _ q b _ q' b').smul continuousOn_const,
      fun x hx v ↦ ?_⟩
    have h := ((b.symm.trans (ContinuousLinearMap.detLineChartEquiv (T x) S.subtypeL q
      (mem_detLineChartSet.1 hx.1)).symm).trans ((ContinuousLinearMap.detLineChartEquiv (T x)
        S'.subtypeL q' (mem_detLineChartSet.1 hx.2)).trans b')).map_smul v 1
    simp only [LinearEquiv.trans_apply, smul_eq_mul, mul_one] at h
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      detLinePretrivialization_symm_apply hT _ q b hx.1,
      detLinePretrivialization_apply_mk hT _ q' b' hx.2, LinearEquiv.apply_symm_apply, h,
      mul_comm]
  totalSpaceMk_isInducing x := by
    obtain ⟨⟨S, _, G, _, q, b, he⟩, hx⟩ := (exists_mem_detLineAtlas hT hF x).choose_spec
    rw [he] at hx ⊢
    exact isInducing_detLinePretrivialization_comp_mk hT _ q b hx

/-- The kernel charts with a finite-dimensional subspace of the target as stabilizer are
pretrivializations of the determinant line bundle, so
`VectorPrebundle.trivializationOfMemPretrivializationAtlas` makes them trivializations of the
bundle. -/
theorem detLinePretrivialization_mem_pretrivializationAtlas (hF : ∀ x, (T x).IsFredholm)
    (S : Submodule 𝕜 F) [FiniteDimensional 𝕜 S] {G : Submodule 𝕜 (E × S)} [FiniteDimensional 𝕜 G]
    (q : E × S →L[𝕜] G) (b : detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (detLine 𝕜 S) ≃ₗ[𝕜] 𝕜) :
    detLinePretrivialization hT S.subtypeL q b ∈
      (detLineVectorPrebundle hT hF).pretrivializationAtlas :=
  ⟨S, inferInstance, G, inferInstance, q, b, rfl⟩

end Bundle

end TauCeti
