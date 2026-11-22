/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.Topology.VectorBundle.Determinant
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

The first Chern class of a complex vector bundle `E` of any constant rank `r` is that of its
determinant line, `c₁(E) = c₁(det E)` with `det E = ⋀ʳ E` (`TauCeti.firstChernClass`, on the
determinant line bundle `TauCeti.DetBundle`). It has the following first properties.

* On a line it is the class above, through the isomorphism `det L ≃ L`
  (`TauCeti.firstChernClass_eq_lineFirstChernClass`).
* It is natural under complex-linear bundle maps over a continuous map of bases
  (`TauCeti.firstChernClass_eq_singularCohomologyMap_of_fiberwise`), in particular under pullback
  (`TauCeti.firstChernClass_pullback`) and bundle isomorphism
  (`TauCeti.firstChernClass_eq_of_fiberwise`), which induce maps of determinant lines.
* It vanishes when `E` has a global frame of continuous sections, whose wedge is a nowhere-zero
  section of `det E` (`TauCeti.firstChernClass_eq_zero_of_linearIndependent`); in particular it
  vanishes for a trivial bundle (`TauCeti.firstChernClass_trivial`) and in rank zero
  (`TauCeti.firstChernClass_eq_zero_of_finrank_eq_zero`), where `det E = ⋀⁰ E` is spanned by the
  empty wedge.

## Implementation notes

The class of a line bundle is named `lineFirstChernClass` because it is defined directly as an
Euler class. The rank hypothesis is `finrank ℂ F = 1`, and the class lives in degree `2`,
definitionally the degree `2 * 0 + 2` of `complexEulerClass` in rank `0 + 1`. Integral
coefficients are `ULift ℤ`, as for the Euler class.

The determinant line `TauCeti.DetBundle ℂ F E` has model fibre `ℂ : Type`, while Euler classes ask
for the base, the fibres and the model fibre to lie in a common universe. So
`TauCeti.firstChernClass` is stated for bases and fibres in `Type`; the model fibre `F` of `E` is
arbitrary. Its naturality under bundle maps compares bundles with the same model fibre, as
`TauCeti.DetBundle.congrHomeomorph` does.

## Main definitions

* `TauCeti.lineFirstChernClass`: the first Chern class `c₁(L) ∈ H²(B; ℤ)` of a complex line bundle,
  the Euler class of its underlying real plane bundle with the complex orientation.
* `TauCeti.firstChernClass`: the first Chern class `c₁(E) = c₁(det E)` of a complex vector bundle.

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

section DeterminantLine

/-! ### The first Chern class of a complex vector bundle -/

variable {B : Type} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]

/-- **The first Chern class of a complex vector bundle** `E → B`: the class
`c₁(E) = c₁(det E) ∈ H²(B; ℤ)` of its determinant line `det E = ⋀ʳ E`, `r` the complex rank of `E`
(`TauCeti.DetBundle`). On a line it is `TauCeti.lineFirstChernClass`
(`TauCeti.firstChernClass_eq_lineFirstChernClass`), and in rank zero it vanishes
(`TauCeti.firstChernClass_eq_zero_of_finrank_eq_zero`). -/
def firstChernClass :
    (TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 :=
  lineFirstChernClass ℂ (DetBundle ℂ F E) (finrank_self ℂ)

/-- The first Chern class of a complex vector bundle is that of its determinant line. -/
theorem firstChernClass_def :
    firstChernClass F E = lineFirstChernClass ℂ (DetBundle ℂ F E) (finrank_self ℂ) :=
  (rfl)

variable {F E}

section BaseMap

variable {B' : Type} [TopologicalSpace B']
  {E' : B' → Type} [TopologicalSpace (TotalSpace F E')] [∀ b, AddCommGroup (E' b)]
  [∀ b, Module ℂ (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F E'] [VectorBundle ℂ F E']

/-- **Naturality of the first Chern class under complex-linear bundle maps.** For a fibrewise
complex-linear isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over a continuous map `g : B' → B`,
continuous on total spaces, between complex vector bundles with the same model fibre,
`c₁(E') = g^* c₁(E)`. -/
theorem firstChernClass_eq_singularCohomologyMap_of_fiberwise {g : C(B', B)}
    {φ : ∀ b', E' b' ≃L[ℂ] E (g b')}
    (hφ : Continuous fun v : TotalSpace F E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.snd)) :
    firstChernClass F E' =
      TopCat.singularCohomologyMap (TopCat.ofHom g) 2 (firstChernClass F E) := by
  -- `φ` is a fibrewise isomorphism `E' ≃ g^* E` over `B'`, continuous on total spaces.
  let φ' : ∀ b', E' b' ≃L[ℂ] ((⇑g) *ᵖ E) b' := φ
  have hφ' : Continuous fun v : TotalSpace F E' ↦
      (⟨v.proj, φ' v.proj v.snd⟩ : TotalSpace F ((⇑g) *ᵖ E)) :=
    (inducing_pullbackTotalSpaceEmbedding F E g).continuous_iff.2
      ((FiberBundle.continuous_proj F E').prodMk hφ)
  -- On determinant lines it induces `det E' ≃ det (g^* E) ≃ g^* det E`, followed by the
  -- projection of the pullback to `det E`.
  refine complexEulerClass_eq_singularCohomologyMap_of_fiberwise (finrank_self ℂ)
    (finrank_self ℂ) (φ := fun b' ↦ (DetBundle.congrEquiv (F := F) φ' b').trans
      (DetBundle.pullbackEquiv (⇑g) b').symm) ?_
  refine ((Pullback.continuous_lift ℂ (DetBundle ℂ F E) (⇑g)).comp
    ((DetBundle.pullbackHomeomorph (F := F) (E := E) g).symm.continuous.comp
      (DetBundle.congrHomeomorph φ' hφ').continuous)).congr fun v ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, DetBundle.pullbackHomeomorph_symm_apply,
    DetBundle.congrHomeomorph_apply]
  -- Pullback fibres are aliases: `(g^* det E)_{b'}` is `det E_{g b'}`, and `Pullback.lift` is the
  -- identity on them, which the pullback rewriting lemmas cannot state at the alias type.
  rfl

/-- **Naturality of the first Chern class under pullback**: for a continuous map `f : B' → B`,
`c₁(f^* E) = f^* c₁(E)`. -/
theorem firstChernClass_pullback (f : C(B', B)) :
    firstChernClass F ((⇑f) *ᵖ E) =
      TopCat.singularCohomologyMap (TopCat.ofHom f) 2 (firstChernClass F E) :=
  firstChernClass_eq_singularCohomologyMap_of_fiberwise
    (φ := fun _ ↦ ContinuousLinearEquiv.refl ℂ _) (Pullback.continuous_lift F E f)

end BaseMap

/-- **Isomorphic complex vector bundles have the same first Chern class.** For a fibrewise
complex-linear isomorphism `φ b : E'_b ≃ E_b`, continuous on total spaces, between complex vector
bundles with the same model fibre, `c₁(E') = c₁(E)`. -/
theorem firstChernClass_eq_of_fiberwise
    {E' : B → Type} [TopologicalSpace (TotalSpace F E')] [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℂ (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F E'] [VectorBundle ℂ F E']
    {φ : ∀ b, E' b ≃L[ℂ] E b}
    (hφ : Continuous fun v : TotalSpace F E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.snd)) :
    firstChernClass F E' = firstChernClass F E :=
  (firstChernClass_eq_singularCohomologyMap_of_fiberwise (g := ContinuousMap.id B) hφ).trans
    (CategoryTheory.ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_id _ _) _)

/-- **A global frame kills the first Chern class.** If `E` has continuous sections `s₁, …, sᵣ`,
`r` its complex rank, which are linearly independent at every point, then `c₁(E) = 0`: the wedge
`s₁ ∧ ⋯ ∧ sᵣ` is a nowhere-zero continuous section of `det E`. -/
theorem firstChernClass_eq_zero_of_linearIndependent {s : Fin (finrank ℂ F) → ∀ b, E b}
    (hs : ∀ i, Continuous fun b ↦ TotalSpace.mk' F b (s i b))
    (hli : ∀ b, LinearIndependent ℂ fun i ↦ s i b) :
    firstChernClass F E = 0 :=
  complexEulerClass_eq_zero_of_forall_ne_zero ℂ (DetBundle ℂ F E) (finrank_self ℂ)
    (DetBundle.continuous_ιMulti hs) fun b ↦
      ((DetBundle.linearEquiv ℂ F E b).symm.map_ne_zero_iff).2
        ((exteriorPower.ιMulti_ne_zero_iff _).2 (hli b))

/-- **The first Chern class of a complex vector bundle of rank zero vanishes**: its determinant
line is spanned by the empty wedge. -/
theorem firstChernClass_eq_zero_of_finrank_eq_zero (hF : finrank ℂ F = 0) :
    firstChernClass F E = 0 := by
  have : IsEmpty (Fin (finrank ℂ F)) := hF ▸ Fin.isEmpty'
  exact firstChernClass_eq_zero_of_linearIndependent (s := isEmptyElim) isEmptyElim
    fun _ ↦ linearIndependent_empty_type

variable (B) in
/-- **The first Chern class of a trivial complex vector bundle vanishes**: the constant sections
given by a basis of `V` form a global frame. -/
@[simp]
theorem firstChernClass_trivial (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] : firstChernClass V (Bundle.Trivial B V) = 0 :=
  firstChernClass_eq_zero_of_linearIndependent (s := fun i _ ↦ Module.finBasis ℂ V i)
    (fun _ ↦ (Bundle.Trivial.homeomorphProd B V).symm.continuous.comp
      (continuous_id.prodMk continuous_const))
    fun _ ↦ (Module.finBasis ℂ V).linearIndependent

end DeterminantLine

section Line

variable {B : Type} [TopologicalSpace B]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]

/-- **On a line, the two first Chern classes agree**: for a complex line bundle `L`,
`c₁(det L) = c₁(L)`, through the isomorphism `det L ≃ L` (`TauCeti.DetBundle.lineEquiv`). -/
theorem firstChernClass_eq_lineFirstChernClass (hF : finrank ℂ F = 1) :
    firstChernClass F E = lineFirstChernClass F E hF :=
  complexEulerClass_eq_of_fiberwise hF (finrank_self ℂ) (DetBundle.continuous_lineEquiv hF)

end Line

end TauCeti
