/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant.Line
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The first Chern class of a complex vector bundle

Let `L → B` be a complex line bundle over a topological space `B`, with model fibre `F` of complex
dimension one. Its underlying real bundle `L_ℝ` is an oriented real plane bundle, each fibre being
oriented by `(v, i v)` for any nonzero `v` (`TauCeti.VectorBundleOrientation.complex`). The
**first Chern class** `c₁(L) ∈ H²(B; ℤ)` (`TauCeti.lineFirstChernClass`) is the Euler class of this
oriented plane bundle, which is `TauCeti.complexEulerClass` in complex rank one.

The laws are the canonical Euler-class laws at `r := 0`, applied directly through
`TauCeti.lineFirstChernClass_def`:

* `TauCeti.complexEulerClass_pullback` and
  `TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise` give naturality under
  continuous pullback and fibrewise complex-linear isomorphisms over a continuous base map;
* `TauCeti.complexEulerClass_eq_of_fiberwise` gives invariance under bundle isomorphism;
* `TauCeti.complexEulerClass_eq_zero_of_forall_ne_zero` and
  `TauCeti.complexEulerClass_trivial` give vanishing for a nowhere-zero section and a trivial line;
* `TauCeti.complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise` gives
  `c₁(L') = -c₁(L)` under a fibrewise conjugate-linear isomorphism; for a continuous base map use
  `TauCeti.complexEulerClass_eq_neg_one_pow_smul_singularCohomologyMap_of_conjugateFiberwise`
  at `r := 0`, simplifying `pow_one` and `neg_one_zsmul`.

The conjugate statement is phrased for an abstract fibrewise conjugate-linear isomorphism, so it
applies to every model of the conjugate line `conj L`, and, through the conjugate-linear Riesz
isomorphism of a Hermitian metric, to the dual line `L*`.

The **first Chern class of a complex vector bundle** `E → B` of any constant rank `r` is the first
Chern class of its determinant line, `c₁(E) = c₁(det E)` (`TauCeti.firstChernClass`), where
`det E = ⋀ʳ E` is `TauCeti.DetBundle ℂ F E`. It satisfies:

* naturality under continuous pullback (`TauCeti.firstChernClass_pullback`) and invariance under
  complex-linear bundle isomorphism (`TauCeti.firstChernClass_eq_of_fiberwise`), since the
  determinant line is natural in both;
* vanishing on trivial bundles (`TauCeti.firstChernClass_trivial`), since `det (B × F)` is the
  trivial line, and in rank zero (`TauCeti.firstChernClass_eq_zero_of_finrank_eq_zero`), since the
  empty exterior product trivializes the determinant line;
* agreement with the first Chern class of a line on line bundles
  (`TauCeti.firstChernClass_eq_lineFirstChernClass`), through `det L ≃ L`.

## Implementation notes

The class `lineFirstChernClass` is the first Chern class of a line bundle, defined directly as an
Euler class. The rank hypothesis is `finrank ℂ F = 1`, and the class lives in degree `2`,
definitionally the degree `2 * 0 + 2` of `complexEulerClass` in rank `0 + 1`. Integral
coefficients are `ULift ℤ`, as for the Euler class.

The class `firstChernClass` is stated for a base and fibres in `Type`: the model fibre of the
determinant line is `ℂ`, and the Euler class takes its model fibre in the universe of the base.

## Main definitions

* `TauCeti.lineFirstChernClass`: the first Chern class `c₁(L) ∈ H²(B; ℤ)` of a complex line bundle,
  the Euler class of its underlying real plane bundle with the complex orientation.
* `TauCeti.firstChernClass`: the first Chern class `c₁(E) ∈ H²(B; ℤ)` of a complex vector bundle,
  the first Chern class of its determinant line.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the top Chern class as the Euler class of the underlying real bundle, and
  Lemma 14.9 on the conjugate bundle).
* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics 82,
  Springer (1982), §20 (the first Chern class of a complex line bundle as its Euler class).
-/

public section

noncomputable section

open Bundle Module

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B]

section Definition

variable (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]
  (hF : finrank ℂ F = 1)

/-- **The first Chern class of a complex line bundle** `L → B`: the class `c₁(L) ∈ H²(B; ℤ)`, the
Euler class of the underlying oriented real plane bundle `L_ℝ` with its complex orientation
`(v, i v)`, that is `complexEulerClass` in complex rank one. -/
def lineFirstChernClass :
    (TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) 2 :=
  complexEulerClass F E (r := 0) hF

/-- The first Chern class of a complex line bundle is the Euler class of its underlying real plane
bundle with the complex orientation. -/
theorem lineFirstChernClass_def :
    lineFirstChernClass F E hF = complexEulerClass F E (r := 0) hF :=
  (rfl)

end Definition

/-! ### The first Chern class of a complex vector bundle -/

section VectorBundle

variable {B : Type} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℂ F E]

/-- **The first Chern class of a complex vector bundle** `E → B`: the class `c₁(E) ∈ H²(B; ℤ)`, the
first Chern class of its determinant line `det E = ⋀ʳ E` (`TauCeti.DetBundle ℂ F E`), a complex
line bundle. -/
def firstChernClass :
    (TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 :=
  lineFirstChernClass ℂ (DetBundle ℂ F E) (finrank_self ℂ)

/-- The first Chern class of a complex vector bundle is the first Chern class of its determinant
line. -/
theorem firstChernClass_def :
    firstChernClass F E = lineFirstChernClass ℂ (DetBundle ℂ F E) (finrank_self ℂ) :=
  (rfl)

/-- **Naturality of the first Chern class.** The first Chern class of the pullback `f*E` along a
continuous map `f : B' → B` is the pull-back along `f` of the first Chern class of `E`. -/
theorem firstChernClass_pullback {B' : Type} [TopologicalSpace B'] (f : C(B', B)) :
    firstChernClass F ((⇑f) *ᵖ E) =
      TopCat.singularCohomologyMap (TopCat.ofHom f) 2 (firstChernClass F E) := by
  rw [firstChernClass_def, firstChernClass_def, lineFirstChernClass_def,
    lineFirstChernClass_def]
  -- `det (f*E)` is `f*(det E)`, which maps to `det E` over `f`.
  refine complexEulerClass_eq_singularCohomologyMap_of_fiberwise _ _ (g := f)
    (φ := fun y ↦ (DetBundle.pullbackEquiv (⇑f) y).symm) ?_
  refine ((Pullback.continuous_lift ℂ (DetBundle ℂ F E) f).comp
    (DetBundle.pullbackHomeomorph f).symm.continuous).congr fun v ↦ ?_
  rw [Function.comp_apply, DetBundle.pullbackHomeomorph_symm_apply]
  -- `Pullback.lift f ⟨y, w⟩ = ⟨f y, w⟩` by definition; `Pullback.lift_mk` does not match here
  -- because the fibre `(f *ᵖ det E) y` is only definitionally `det E (f y)`.
  rfl

/-- **Isomorphic complex vector bundles have the same first Chern class.** For a fibrewise
complex-linear isomorphism `φ b : E_b ≃ E'_b`, continuous on total spaces, `c₁(E) = c₁(E')`. -/
theorem firstChernClass_eq_of_fiberwise {E' : B → Type} [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℂ (E' b)] [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    [FiberBundle F E'] [VectorBundle ℂ F E'] {φ : ∀ b, E b ≃L[ℂ] E' b}
    (hφ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F v.proj (φ v.proj v.snd)) :
    firstChernClass F E = firstChernClass F E' :=
  complexEulerClass_eq_of_fiberwise _ _ (φ := DetBundle.congrEquiv φ)
    ((DetBundle.congrHomeomorph φ hφ).continuous.congr (DetBundle.congrHomeomorph_apply φ hφ))

/-- **The first Chern class vanishes in rank zero**: the determinant line of a bundle of rank zero
has the nowhere-vanishing continuous section given by the empty exterior product. -/
theorem firstChernClass_eq_zero_of_finrank_eq_zero (hF : finrank ℂ F = 0) :
    firstChernClass F E = 0 :=
  complexEulerClass_eq_zero_of_forall_ne_zero _ _ _ (DetBundle.continuous_rankZeroSection hF)
    (DetBundle.rankZeroSection_ne_zero hF)

end VectorBundle

section Trivial

variable (B : Type) [TopologicalSpace B] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- **The first Chern class of a trivial complex vector bundle vanishes**: the determinant line of
`B × F` is the trivial line `B × ℂ`. -/
@[simp]
theorem firstChernClass_trivial : firstChernClass F (Bundle.Trivial B F) = 0 := by
  rw [firstChernClass_def, lineFirstChernClass_def,
    complexEulerClass_eq_of_fiberwise (finrank_self ℂ) _ (E := Bundle.Trivial B ℂ)
      (φ := DetBundle.trivialEquiv ℂ B F) ((DetBundle.trivialHomeomorph ℂ B F).continuous.congr
        DetBundle.trivialHomeomorph_apply)]
  exact complexEulerClass_trivial B ℂ _

end Trivial

section Line

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]

/-- **On a line bundle the two first Chern classes agree.** For a complex line bundle `L`, the first
Chern class `c₁(det L)` of its determinant line is the Euler class `c₁(L)` of its underlying
oriented real plane bundle, through the identification `det L ≃ L`. -/
theorem firstChernClass_eq_lineFirstChernClass (hF : finrank ℂ F = 1) :
    firstChernClass F E = lineFirstChernClass F E hF :=
  complexEulerClass_eq_of_fiberwise hF (finrank_self ℂ) (φ := DetBundle.lineEquiv hF)
    ((DetBundle.lineHomeomorph hF).continuous.congr (DetBundle.lineHomeomorph_apply hF))

end Line

end TauCeti
