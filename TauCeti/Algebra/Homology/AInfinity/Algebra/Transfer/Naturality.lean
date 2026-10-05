/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.BarDifferential
public import TauCeti.Algebra.Homology.Contraction.Naturality
public import TauCeti.Algebra.Homology.Contraction.TensorTrick.Naturality

/-!
# Naturality of homological transfer

A strict morphism of `A∞` algebras, together with a degree-zero map of their retracts commuting
with inclusion, projection and homotopy, induces a strict morphism of the transferred structures.
The extending inclusion and projection morphisms form commuting squares with these maps.
In particular the retract map preserves every transferred operation, not just the unary complex
or the induced cohomology product.

The hypotheses express compatibility with the chosen contractions. No field or minimality
assumption is required. This does not assert that arbitrary maps preserve arbitrary choices of
transferred structures strictly.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
-/

public section

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

universe uR uA uH uB uK

variable {R : Type uR} [CommRing R]
  {A : Type uA} {H : Type uH} {B : Type uB} {K : Type uK}
  [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]
  [AddCommGroup B] [Module R B] [AddCommGroup K] [Module R K]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}
  {GH : InternalGrading R H} {GK : InternalGrading R K}
  {dH : Module.End R H} {dK : Module.End R K}
  (c : LinearSpecialContraction 𝒜.differential dH)
  (c' : LinearSpecialContraction ℬ.differential dK)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hi : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hp : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)
  (hh' : LinearMap.IsHomogeneous c'.homotopy ℬ.grading.piece ℬ.grading.piece (-1))
  (hi' : LinearMap.IsHomogeneous c'.incl GK.piece ℬ.grading.piece 0)
  (hp' : LinearMap.IsHomogeneous c'.proj ℬ.grading.piece GK.piece 0)
  (f : AInfinityStrictHom 𝒜 ℬ) (g : H →ₗ[R] K)
  (hι : f.toLinearMap ∘ₗ c.incl = c'.incl ∘ₗ g)
  (hπ : g ∘ₗ c.proj = c'.proj ∘ₗ f.toLinearMap)
  (hη : f.toLinearMap ∘ₗ c.homotopy = c'.homotopy ∘ₗ f.toLinearMap)

include hι in
private theorem bar_incl_naturality :
    f.barMap ∘ₗ (𝒜.barTensorTrick c hh hi hp).incl =
      (ℬ.barTensorTrick c' hh' hi' hp').incl ∘ₗ ReducedTensorWords.map (R := R) g := by
  simp only [barTensorTrick_incl, AInfinityStrictHom.barMap_def, ← map_comp, hι]

include hπ in
private theorem bar_proj_naturality :
    ReducedTensorWords.map (R := R) g ∘ₗ (𝒜.barTensorTrick c hh hi hp).proj =
      (ℬ.barTensorTrick c' hh' hi' hp').proj ∘ₗ f.barMap := by
  simp only [barTensorTrick_proj, AInfinityStrictHom.barMap_def, ← map_comp, hπ]

include hι hπ hη in
private theorem bar_homotopy_naturality :
    f.barMap ∘ₗ (𝒜.barTensorTrick c hh hi hp).homotopy =
      (ℬ.barTensorTrick c' hh' hi' hp').homotopy ∘ₗ f.barMap := by
  rw [barTensorTrick_homotopy, barTensorTrick_homotopy, AInfinityStrictHom.barMap_def]
  exact c.reducedTensorWordsHomotopy_naturality c' f.toLinearMap g
    (f.isHomogeneous_shift 1) hι hπ hη

include hι hπ hη in
/-- The letterwise retract map intertwines the transferred bar differentials. -/
theorem transferBarDifferential_naturality :
    ReducedTensorWords.map (R := R) g ∘ₗ 𝒜.transferBarDifferential c hh hi hp =
      ℬ.transferBarDifferential c' hh' hi' hp' ∘ₗ ReducedTensorWords.map (R := R) g := by
  have hdbar : ReducedTensorWords.map (R := R) g ∘ₗ
      gradedCoderiv (GH.shift 1) (dH ∘ₗ letter R H) 1 =
        gradedCoderiv (GK.shift 1) (dK ∘ₗ letter R K) 1 ∘ₗ
          ReducedTensorWords.map (R := R) g := by
    -- Use the unperturbed inclusion square, the unary bar chain map, and the bar projection.
    have h := bar_incl_naturality c c' hh hi hp hh' hi' hp' f g hι
    have hchain := (𝒜.barTensorTrick c hh hi hp).dM_comp_incl
    have hchain' := (ℬ.barTensorTrick c' hh' hi' hp').dM_comp_incl
    have hf := f.unaryBarDifferential_comp_barMap
    rw [unaryBarDifferential_eq_gradedCoderiv, unaryBarDifferential_eq_gradedCoderiv] at hf
    simp only [LinearMap.ext_iff, LinearMap.comp_apply] at h hchain hchain' hf
    apply LinearMap.ext
    intro x
    have he : (ℬ.barTensorTrick c' hh' hi' hp').incl
        (ReducedTensorWords.map (R := R) g (gradedCoderiv (GH.shift 1) (dH ∘ₗ letter R H) 1 x)) =
          (ℬ.barTensorTrick c' hh' hi' hp').incl
            (gradedCoderiv (GK.shift 1) (dK ∘ₗ letter R K) 1
              (ReducedTensorWords.map (R := R) g x)) := by grind only
    simpa only [LinearMap.comp_apply, LinearSpecialContraction.proj_incl_apply] using
      congrArg (ℬ.barTensorTrick c' hh' hi' hp').proj he
  simp only [transferBarDifferential_def]
  exact (𝒜.barTensorTrick c hh hi hp).perturbedDifferential_naturality
    (ℬ.barTensorTrick c' hh' hi' hp') f.barMap (ReducedTensorWords.map (R := R) g)
    (bar_incl_naturality c c' hh hi hp hh' hi' hp' f g hι)
    (bar_proj_naturality c c' hh hi hp hh' hi' hp' f g hπ)
    (bar_homotopy_naturality c c' hh hi hp hh' hi' hp' f g hι hπ hη)
    hdbar f.higherBarDifferential_comp_barMap.symm
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hi hp)
    (ℬ.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c' hh' hi' hp')

include hι hπ hη

/-- The morphism between transferred structures induced by a strict morphism and compatible
contractions. Its bar map is the letterwise retract map. -/
private noncomputable def transferBarHom :
    AInfinityHom (𝒜.transfer c hh hi hp) (ℬ.transfer c' hh' hi' hp') where
  barMap := ReducedTensorWords.map (R := R) g
  isCoalgHom_barMap := isCoalgHom_map g
  isHomogeneous_barMap := by
    rw [transfer_grading, transfer_grading]
    apply isHomogeneous_map
    apply LinearMap.isHomogeneous_shift_piece_iff.mpr
    have he : c'.proj ∘ₗ f.toLinearMap ∘ₗ c.incl = g := by
      rw [hι, c'.proj_comp_incl_assoc]
    rw [← he]
    simpa only [zero_add] using hp'.comp (f.isHomogeneous.comp hi)
  barDifferential_comp_barMap := by
    rw [barDifferential_transfer, barDifferential_transfer]
    exact (transferBarDifferential_naturality c c' hh hi hp hh' hi' hp' f g hι hπ hη).symm

/-- The induced morphism acts letterwise by the retract map on the bar construction. -/
private theorem barMap_transferBarHom :
    (transferBarHom c c' hh hi hp hh' hi' hp' f g hι hπ hη).barMap =
      ReducedTensorWords.map (R := R) g := (rfl)

/-- The linear part of the induced morphism is the original retract map. -/
private theorem linearPart_transferBarHom :
    (transferBarHom c c' hh hi hp hh' hi' hp' f g hι hπ hη).linearPart = g := by
  apply LinearMap.ext
  intro x
  rw [AInfinityHom.linearPart_apply, AInfinityHom.taylor_def, barMap_transferBarHom,
    LinearMap.comp_apply, map_ofLetter, letter_ofLetter]

/-- Transfer sends compatible strict morphisms to strict morphisms. -/
private theorem isStrict_transferBarHom :
    (transferBarHom c c' hh hi hp hh' hi' hp' f g hι hπ hη).IsStrict := by
  rw [AInfinityHom.isStrict_iff, AInfinityHom.taylor_def, barMap_transferBarHom,
    linearPart_transferBarHom, letter_comp_map]

/-- The strict morphism between transferred structures induced by a strict morphism and
compatible contractions. Its underlying linear map is the retract map. -/
noncomputable def transferStrictHom :
    AInfinityStrictHom (𝒜.transfer c hh hi hp) (ℬ.transfer c' hh' hi' hp') :=
  (isStrict_transferBarHom c c' hh hi hp hh' hi' hp' f g hι hπ hη).toStrictHom

/-- The underlying linear map of the induced strict morphism is the retract map. -/
@[simp]
theorem transferStrictHom_toLinearMap :
    (transferStrictHom c c' hh hi hp hh' hi' hp' f g hι hπ hη).toLinearMap = g := by
  rw [transferStrictHom, AInfinityHom.IsStrict.toStrictHom_toLinearMap,
    linearPart_transferBarHom]

/-- The induced strict morphism acts by the retract map. -/
@[simp]
theorem coe_transferStrictHom :
    ⇑(transferStrictHom c c' hh hi hp hh' hi' hp' f g hι hπ hη) = g := by
  rw [← AInfinityStrictHom.coe_toLinearMap, transferStrictHom_toLinearMap]

/-- The induced strict morphism acts letterwise on the bar construction. -/
@[simp]
theorem barMap_transferStrictHom :
    (transferStrictHom c c' hh hi hp hh' hi' hp' f g hι hπ hη).barMap =
      ReducedTensorWords.map (R := R) g := by
  rw [AInfinityStrictHom.barMap_def, transferStrictHom_toLinearMap]

/-- The retract map preserves all transferred operations. -/
-- The target contraction and strict morphism cannot be inferred from the left-hand side,
-- so `@[simp]` would fail the `simpNF` linter. Supply them explicitly when using `simp`.
theorem map_m_transfer (n : ℕ) (x : Fin n → H) :
    g ((𝒜.transfer c hh hi hp).m n x) =
      (ℬ.transfer c' hh' hi' hp').m n (fun i ↦ g (x i)) := by
  simpa only [coe_transferStrictHom] using
    (transferStrictHom c c' hh hi hp hh' hi' hp' f g hι hπ hη).map_m n x

/-- The extending inclusion is natural under maps compatible with the contractions. -/
theorem transferInclusion_naturality :
    f.toAInfinityHom.comp (𝒜.transferInclusion c hh hi hp) =
      (ℬ.transferInclusion c' hh' hi' hp').comp
        (transferStrictHom c c' hh hi hp hh' hi' hp' f g hι hπ hη).toAInfinityHom := by
  apply AInfinityHom.barMap_injective
  simp only [AInfinityHom.barMap_comp, AInfinityStrictHom.barMap_toAInfinityHom,
    barMap_transferStrictHom]
  -- Use the basic perturbation lemma on the tensor-trick contractions.
  have h := (𝒜.barTensorTrick c hh hi hp).perturb_incl_naturality
    (ℬ.barTensorTrick c' hh' hi' hp') f.barMap (ReducedTensorWords.map (R := R) g)
    𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
    ℬ.gradedCoderiv_differential_add_higherBarDifferential_comp_self
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hi hp)
    (ℬ.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c' hh' hi' hp')
    (bar_incl_naturality c c' hh hi hp hh' hi' hp' f g hι)
    (bar_homotopy_naturality c c' hh hi hp hh' hi' hp' f g hι hπ hη)
    f.higherBarDifferential_comp_barMap.symm
  simpa only [LinearSpecialContraction.perturb_incl, barTensorTrick_incl,
    barTensorTrick_homotopy, barMap_transferInclusion] using h

/-- The projection onto the transferred structure is natural under compatible maps. -/
theorem transferProjection_naturality :
    (transferStrictHom c c' hh hi hp hh' hi' hp' f g hι hπ hη).toAInfinityHom.comp
        (𝒜.transferProjection c hh hi hp) =
      (ℬ.transferProjection c' hh' hi' hp').comp f.toAInfinityHom := by
  apply AInfinityHom.barMap_injective
  simp only [AInfinityHom.barMap_comp, AInfinityStrictHom.barMap_toAInfinityHom,
    barMap_transferStrictHom]
  have h := (𝒜.barTensorTrick c hh hi hp).perturb_proj_naturality
    (ℬ.barTensorTrick c' hh' hi' hp') f.barMap (ReducedTensorWords.map (R := R) g)
    𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
    ℬ.gradedCoderiv_differential_add_higherBarDifferential_comp_self
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hi hp)
    (ℬ.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c' hh' hi' hp')
    (bar_proj_naturality c c' hh hi hp hh' hi' hp' f g hπ)
    (bar_homotopy_naturality c c' hh hi hp hh' hi' hp' f g hι hπ hη)
    f.higherBarDifferential_comp_barMap.symm
  simpa only [LinearSpecialContraction.perturb_proj, barTensorTrick_proj,
    barTensorTrick_homotopy, barMap_transferProjection] using h

end TauCeti.AInfinityAlgebra
