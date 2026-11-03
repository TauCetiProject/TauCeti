/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import TauCeti.Topology.Algebra.Group.UCB.Translation

/-!
# Inversion and the two uniform-continuity conventions

`TauCeti.rightUcbSubalgebra 𝕜 G` consists of bounded continuous functions for which `f (x * u)`
is uniformly close to `f x` as `u → 1`. This is uniform continuity for Mathlib's
`IsTopologicalGroup.leftUniformSpace`, in contrast to `TauCeti.ucbSubalgebra 𝕜 G`, which uses the
right uniformity. These spaces need not agree. The real space is `TauCeti.rightUcb G`, with
carrier type `TauCeti.RightUCB G`.

Precomposition by inversion gives the algebra equivalence `TauCeti.ucbSubalgebra.invEquiv`
between the two spaces over any normed field, with real specialization `TauCeti.UCB.invEquiv`.
It preserves the supremum norm, and in the real
case pointwise order, and exchanges left translation `f (g⁻¹ * ·)` with right translation
`f (· * g)`. Thus function-space constructions can be transported between the two conventions
without assuming that the group is a uniform group.

The right-multiplication space is defined as the pullback of `ucbSubalgebra 𝕜 G`,
so it inherits its algebra operations. The real space is closed under uniform limits.
The comparison of uniformities reuses Mathlib's `UniformEquiv.inv`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3 and G.1.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

variable {𝕜 G : Type*} [NormedField 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (𝕜 G) in
/-- The subalgebra of bounded continuous functions uniformly continuous under small right
multiplication. Equivalently, precomposing with inversion gives an element of
`ucbSubalgebra 𝕜 G`. -/
def rightUcbSubalgebra : Subalgebra 𝕜 (G →ᵇ 𝕜) :=
  (ucbSubalgebra 𝕜 G).comap
    { toFun := fun f => f.compContinuous ⟨Inv.inv, continuous_inv⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

/-- Membership in the right-multiplication space is membership in `ucbSubalgebra 𝕜 G`
after inversion. -/
theorem mem_rightUcbSubalgebra_iff_comp_inv {f : G →ᵇ 𝕜} :
    f ∈ rightUcbSubalgebra 𝕜 G ↔
      f.compContinuous ⟨Inv.inv, continuous_inv⟩ ∈ ucbSubalgebra 𝕜 G :=
  Iff.rfl

/-- The defining right-multiplication condition. -/
theorem mem_rightUcbSubalgebra_iff {f : G →ᵇ 𝕜} :
    f ∈ rightUcbSubalgebra 𝕜 G ↔
      ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, ‖f (x * u) - f x‖ < ε := by
  rw [mem_rightUcbSubalgebra_iff_comp_inv, mem_ucbSubalgebra_iff]
  constructor
  · intro h ε hε
    filter_upwards [(tendsto_inv (1 : G)).eventually (by simpa using h ε hε)] with u hu x
    simpa using hu x⁻¹
  · intro h ε hε
    filter_upwards [(tendsto_inv (1 : G)).eventually (by simpa using h ε hε)] with u hu x
    simpa using hu x⁻¹

/-- The right-multiplication condition is uniform continuity for Mathlib's left uniformity. -/
theorem mem_rightUcbSubalgebra_iff_uniformContinuous {f : G →ᵇ 𝕜} :
    f ∈ rightUcbSubalgebra 𝕜 G ↔
      (letI : UniformSpace G := IsTopologicalGroup.leftUniformSpace G
       UniformContinuous f) := by
  rw [mem_rightUcbSubalgebra_iff_comp_inv, mem_ucbSubalgebra_iff]
  simp only [← dist_eq_norm, ← uniformContinuous_rightUniformSpace_iff]
  -- Both functions of Mathlib's inversion equivalence are inversion, but the uniform
  -- structures differ. Specify them explicitly when composing uniform-continuity proofs.
  have hrl : @UniformContinuous G G (IsTopologicalGroup.rightUniformSpace G)
      (IsTopologicalGroup.leftUniformSpace G) Inv.inv :=
    @UniformEquiv.uniformContinuous_toFun G G (IsTopologicalGroup.rightUniformSpace G)
      (IsTopologicalGroup.leftUniformSpace G) (UniformEquiv.inv G)
  have hlr : @UniformContinuous G G (IsTopologicalGroup.leftUniformSpace G)
      (IsTopologicalGroup.rightUniformSpace G) Inv.inv :=
    @UniformEquiv.uniformContinuous_invFun G G (IsTopologicalGroup.rightUniformSpace G)
      (IsTopologicalGroup.leftUniformSpace G) (UniformEquiv.inv G)
  constructor
  · intro h
    simpa only [Function.comp_def, inv_inv] using
      @UniformContinuous.comp G G 𝕜 (IsTopologicalGroup.leftUniformSpace G)
        (IsTopologicalGroup.rightUniformSpace G) _ (fun x => f x⁻¹) Inv.inv h hlr
  · intro h
    exact @UniformContinuous.comp G G 𝕜 (IsTopologicalGroup.rightUniformSpace G)
      (IsTopologicalGroup.leftUniformSpace G) _ (f : G → 𝕜) Inv.inv h hrl

variable (G) in
/-- The subalgebra of real bounded continuous functions uniformly continuous under small right
multiplication, the case `𝕜 = ℝ` of `rightUcbSubalgebra 𝕜 G`. -/
def rightUcb : Subalgebra ℝ (G →ᵇ ℝ) :=
  rightUcbSubalgebra ℝ G

variable (G) in
/-- The real Banach algebra of bounded functions uniformly continuous under small right
multiplication, with the inherited supremum norm and pointwise order. -/
abbrev RightUCB : Type _ := rightUcb G

variable (G) in
/-- `rightUcb G` is the case `𝕜 = ℝ` of `rightUcbSubalgebra 𝕜 G`. -/
theorem rightUcb_eq_rightUcbSubalgebra : rightUcb G = rightUcbSubalgebra ℝ G :=
  (rfl)

/-- Membership in the real right-multiplication space is membership in `ucb G` after inversion. -/
theorem mem_rightUcb_iff_comp_inv {f : G →ᵇ ℝ} :
    f ∈ rightUcb G ↔ f.compContinuous ⟨Inv.inv, continuous_inv⟩ ∈ ucb G :=
  mem_rightUcbSubalgebra_iff_comp_inv

/-- The defining right-multiplication condition for real functions. -/
theorem mem_rightUcb_iff {f : G →ᵇ ℝ} :
    f ∈ rightUcb G ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, |f (x * u) - f x| < ε := by
  simp only [rightUcb_eq_rightUcbSubalgebra, mem_rightUcbSubalgebra_iff, Real.norm_eq_abs]

/-- The real right-multiplication condition is uniform continuity for Mathlib's left uniformity. -/
theorem mem_rightUcb_iff_uniformContinuous {f : G →ᵇ ℝ} :
    f ∈ rightUcb G ↔
      (letI : UniformSpace G := IsTopologicalGroup.leftUniformSpace G
       UniformContinuous f) :=
  mem_rightUcbSubalgebra_iff_uniformContinuous

/-- The real right-multiplication space is closed under uniform limits. -/
theorem isClosed_rightUcb : IsClosed (rightUcb G : Set (G →ᵇ ℝ)) :=
  isClosed_ucb.preimage
    (BoundedContinuousFunction.compContinuousCLM ℝ ℝ ⟨Inv.inv, continuous_inv⟩).continuous

/-- The supremum norm on the right-multiplication space is the inherited norm. -/
instance : NormedAddCommGroup (RightUCB G) := inferInstance

/-- The right-multiplication space is complete for the supremum norm. -/
instance : CompleteSpace (RightUCB G) := isClosed_rightUcb.completeSpace_coe

namespace RightUCB

/-- Two functions in the right-multiplication space agree if they agree pointwise. -/
@[ext]
theorem ext {f h : RightUCB G} (heq : ∀ x, (f : G →ᵇ ℝ) x = (h : G →ᵇ ℝ) x) : f = h :=
  Subtype.ext (BoundedContinuousFunction.ext heq)

/-- The order in the right-multiplication space is the pointwise order. -/
theorem le_def {f h : RightUCB G} : f ≤ h ↔ ∀ x, (f : G →ᵇ ℝ) x ≤ (h : G →ᵇ ℝ) x :=
  Iff.rfl

end RightUCB

namespace ucbSubalgebra

variable (𝕜 G) in
/-- Precomposition by inversion identifies the two uniform-continuity conventions as algebras.
It does not assert that either space is preserved by inversion. -/
def invEquiv : ucbSubalgebra 𝕜 G ≃ₐ[𝕜] rightUcbSubalgebra 𝕜 G where
  toFun f := ⟨(f : G →ᵇ 𝕜).compContinuous ⟨Inv.inv, continuous_inv⟩,
    mem_rightUcbSubalgebra_iff_comp_inv.2 (by
      have hinv : ((f : G →ᵇ 𝕜).compContinuous ⟨Inv.inv, continuous_inv⟩).compContinuous
          ⟨Inv.inv, continuous_inv⟩ = (f : G →ᵇ 𝕜) := by ext x; simp
      rw [hinv]
      exact f.2)⟩
  invFun f := ⟨(f : G →ᵇ 𝕜).compContinuous ⟨Inv.inv, continuous_inv⟩,
    mem_rightUcbSubalgebra_iff_comp_inv.1 f.2⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Inversion of a function is precomposition with the continuous inversion map. -/
theorem coe_invEquiv (f : ucbSubalgebra 𝕜 G) :
    (invEquiv 𝕜 G f : G →ᵇ 𝕜) = (f : G →ᵇ 𝕜).compContinuous ⟨Inv.inv, continuous_inv⟩ :=
  (rfl)

@[simp]
theorem invEquiv_apply (f : ucbSubalgebra 𝕜 G) (x : G) :
    (invEquiv 𝕜 G f : G →ᵇ 𝕜) x = (f : G →ᵇ 𝕜) x⁻¹ :=
  (rfl)

/-- The inverse equivalence is also precomposition with inversion. -/
theorem coe_invEquiv_symm (f : rightUcbSubalgebra 𝕜 G) :
    ((invEquiv 𝕜 G).symm f : G →ᵇ 𝕜) =
      (f : G →ᵇ 𝕜).compContinuous ⟨Inv.inv, continuous_inv⟩ :=
  (rfl)

@[simp]
theorem invEquiv_symm_apply (f : rightUcbSubalgebra 𝕜 G) (x : G) :
    ((invEquiv 𝕜 G).symm f : G →ᵇ 𝕜) x = (f : G →ᵇ 𝕜) x⁻¹ :=
  (rfl)

/-- Inversion preserves the supremum norm. -/
@[simp]
theorem norm_invEquiv (f : ucbSubalgebra 𝕜 G) :
    ‖(invEquiv 𝕜 G f : G →ᵇ 𝕜)‖ = ‖(f : G →ᵇ 𝕜)‖ := by
  apply le_antisymm
  · exact (f : G →ᵇ 𝕜).norm_compContinuous_le _
  · have h := (invEquiv 𝕜 G f : G →ᵇ 𝕜).norm_compContinuous_le
        (⟨Inv.inv, continuous_inv⟩ : C(G, G))
    simpa only [← coe_invEquiv_symm, AlgEquiv.symm_apply_apply] using h

/-- The inverse identification also preserves the supremum norm. -/
@[simp]
theorem norm_invEquiv_symm (f : rightUcbSubalgebra 𝕜 G) :
    ‖((invEquiv 𝕜 G).symm f : G →ᵇ 𝕜)‖ = ‖(f : G →ᵇ 𝕜)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (norm_invEquiv ((invEquiv 𝕜 G).symm f)).symm

variable (𝕜 G) in
/-- Inversion as a linear isometry equivalence for the supremum norms. -/
def invLinearIsometryEquiv : ucbSubalgebra 𝕜 G ≃ₗᵢ[𝕜] rightUcbSubalgebra 𝕜 G :=
  { (invEquiv 𝕜 G).toLinearEquiv with norm_map' := norm_invEquiv }

@[simp]
theorem invLinearIsometryEquiv_apply (f : ucbSubalgebra 𝕜 G) :
    invLinearIsometryEquiv 𝕜 G f = invEquiv 𝕜 G f :=
  (rfl)

@[simp]
theorem invLinearIsometryEquiv_symm_apply (f : rightUcbSubalgebra 𝕜 G) :
    (invLinearIsometryEquiv 𝕜 G).symm f = (invEquiv 𝕜 G).symm f :=
  (rfl)

end ucbSubalgebra

namespace UCB

-- Specialize the domain and codomain to the named real spaces: simp does not unfold
-- ucb and rightUcb when matching the scalar-general evaluation and norm lemmas.
variable (G) in
/-- Precomposition by inversion identifies the real uniform-continuity spaces as algebras,
the case `𝕜 = ℝ` of `ucbSubalgebra.invEquiv`. -/
def invEquiv : UCB G ≃ₐ[ℝ] RightUCB G :=
  ucbSubalgebra.invEquiv ℝ G

/-- Inversion of a real function is precomposition with the continuous inversion map. -/
theorem coe_invEquiv (f : UCB G) :
    (invEquiv G f : G →ᵇ ℝ) = (f : G →ᵇ ℝ).compContinuous ⟨Inv.inv, continuous_inv⟩ :=
  ucbSubalgebra.coe_invEquiv f

@[simp]
theorem invEquiv_apply (f : UCB G) (x : G) :
    (invEquiv G f : G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x⁻¹ :=
  ucbSubalgebra.invEquiv_apply f x

/-- The inverse real equivalence is also precomposition with inversion. -/
theorem coe_invEquiv_symm (f : RightUCB G) :
    ((invEquiv G).symm f : G →ᵇ ℝ) =
      (f : G →ᵇ ℝ).compContinuous ⟨Inv.inv, continuous_inv⟩ :=
  ucbSubalgebra.coe_invEquiv_symm f

@[simp]
theorem invEquiv_symm_apply (f : RightUCB G) (x : G) :
    ((invEquiv G).symm f : G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x⁻¹ :=
  ucbSubalgebra.invEquiv_symm_apply f x

/-- Inversion preserves the real supremum norm. -/
@[simp]
theorem norm_invEquiv (f : UCB G) :
    ‖(invEquiv G f : G →ᵇ ℝ)‖ = ‖(f : G →ᵇ ℝ)‖ :=
  ucbSubalgebra.norm_invEquiv f

/-- The inverse real identification also preserves the supremum norm. -/
@[simp]
theorem norm_invEquiv_symm (f : RightUCB G) :
    ‖((invEquiv G).symm f : G →ᵇ ℝ)‖ = ‖(f : G →ᵇ ℝ)‖ :=
  ucbSubalgebra.norm_invEquiv_symm f

variable (G) in
/-- Inversion as a real linear isometry equivalence, the case `𝕜 = ℝ` of
`ucbSubalgebra.invLinearIsometryEquiv`. -/
def invLinearIsometryEquiv : UCB G ≃ₗᵢ[ℝ] RightUCB G :=
  ucbSubalgebra.invLinearIsometryEquiv ℝ G

@[simp]
theorem invLinearIsometryEquiv_apply (f : UCB G) :
    invLinearIsometryEquiv G f = invEquiv G f :=
  (rfl)

@[simp]
theorem invLinearIsometryEquiv_symm_apply (f : RightUCB G) :
    (invLinearIsometryEquiv G).symm f = (invEquiv G).symm f :=
  (rfl)

/-- Inversion preserves and reflects pointwise order. -/
@[simp]
theorem invEquiv_le_invEquiv_iff {f h : UCB G} :
    invEquiv G f ≤ invEquiv G h ↔ f ≤ h := by
  simp only [RightUCB.le_def, invEquiv_apply, le_def]
  exact ((Equiv.inv G).surjective.forall
    (p := fun x => (f : G →ᵇ ℝ) x ≤ (h : G →ᵇ ℝ) x)).symm

/-- Inversion exchanges left translation by `g` with right translation by `g`. -/
theorem invEquiv_leftTranslation (g : G) (f : UCB G) :
    (invEquiv G (leftTranslation g f) : G →ᵇ ℝ) =
      (invEquiv G f : G →ᵇ ℝ).compContinuous (ContinuousMap.mulRight g) := by
  ext x
  simp

/-- Inversion exchanges right translation by `g` with left translation by `g`. -/
theorem invEquiv_rightTranslation (g : G) (f : UCB G) :
    (invEquiv G (rightTranslation g f) : G →ᵇ ℝ) =
      (invEquiv G f : G →ᵇ ℝ).compContinuous (ContinuousMap.mulLeft g⁻¹) := by
  ext x
  simp

end UCB

end TauCeti
