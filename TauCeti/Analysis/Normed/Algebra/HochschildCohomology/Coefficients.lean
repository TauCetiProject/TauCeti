/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HochschildCohomology.Coboundary

/-!
# Change of coefficients for bounded Hochschild cochains

Postcomposition by a bounded bimodule map commutes with every Hochschild coface and hence
with the bounded Hochschild differential. The cochain map is Mathlib's existing
`ContinuousLinearMap.compContinuousMultilinearMapL`; in particular its norm estimates,
identity law and composition law require no new cochain construction.

The pointwise and operator forms of naturality are provided here. An injective coefficient
map reflects cocycles. A coefficient map with a bounded bimodule retraction also reflects
coboundaries: a primitive in the larger module can be projected back to the smaller one.
These results use actual coboundaries, not their norm closures.

The actions are bounded bilinear maps and need not be unital or contractive. Naturality
uses only intertwining of the actions, so associativity and the bimodule laws are not
needed for these identities. Neither the algebra nor the coefficient spaces need be complete.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.8.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 A E F : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {L R : A →L[𝕜] E →L[𝕜] E} {L' R' : A →L[𝕜] F →L[𝕜] F} {n : ℕ}

/-- A bounded map intertwining the two actions commutes with every Hochschild coface. -/
theorem hochschildBimoduleCoface_compContinuousMultilinearMap (f : E →L[𝕜] F)
    (hL : ∀ a x, f (L a x) = L' a (f x))
    (hR : ∀ a x, f (R a x) = R' a (f x))
    (i : Fin (n + 2)) (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) :
    hochschildBimoduleCoface L' R' i (f.compContinuousMultilinearMap T) =
      f.compContinuousMultilinearMap (hochschildBimoduleCoface L R i T) := by
  ext a
  induction i using Fin.cases with
  | zero =>
    simp only [hochschildBimoduleCoface_zero_apply, compContinuousMultilinearMap_coe,
      Function.comp_apply, hL]
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.succ_last, hochschildBimoduleCoface_last_apply,
        compContinuousMultilinearMap_coe, Function.comp_apply, hR]
    | cast j =>
      simp only [hochschildBimoduleCoface_castSucc_succ_apply,
        compContinuousMultilinearMap_coe, Function.comp_apply]

/-- Postcomposition by a bounded bimodule map commutes with the bounded Hochschild
coboundary in every degree. -/
theorem hochschildBimoduleCoboundary_compContinuousMultilinearMap (f : E →L[𝕜] F)
    (hL : ∀ a x, f (L a x) = L' a (f x))
    (hR : ∀ a x, f (R a x) = R' a (f x))
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) :
    hochschildBimoduleCoboundary L' R' n (f.compContinuousMultilinearMap T) =
      f.compContinuousMultilinearMap (hochschildBimoduleCoboundary L R n T) := by
  ext a
  simp only [hochschildBimoduleCoboundary_apply,
    hochschildBimoduleCoface_compContinuousMultilinearMap f hL hR,
    compContinuousMultilinearMap_coe, Function.comp_apply, map_sum, map_zsmul]

/-- The operator form of coefficient naturality: postcomposition is a bounded cochain map. -/
theorem hochschildBimoduleCoboundary_comp_compContinuousMultilinearMapL (f : E →L[𝕜] F)
    (hL : ∀ a x, f (L a x) = L' a (f x))
    (hR : ∀ a x, f (R a x) = R' a (f x)) :
    hochschildBimoduleCoboundary L' R' n ∘L
        compContinuousMultilinearMapL 𝕜 (fun _ : Fin n ↦ A) E F f =
      compContinuousMultilinearMapL 𝕜 (fun _ : Fin (n + 1) ↦ A) E F f ∘L
        hochschildBimoduleCoboundary L R n := by
  ext T a
  exact congrArg (fun S ↦ S a)
    (hochschildBimoduleCoboundary_compContinuousMultilinearMap f hL hR T)

/-- An injective bounded bimodule map preserves and reflects Hochschild cocycles. -/
theorem hochschildBimoduleCoboundary_comp_eq_zero_iff_of_injective
    (f : E →L[𝕜] F) (hL : ∀ a x, f (L a x) = L' a (f x))
    (hR : ∀ a x, f (R a x) = R' a (f x)) (hf : Function.Injective f)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) :
    hochschildBimoduleCoboundary L' R' n (f.compContinuousMultilinearMap T) = 0 ↔
      hochschildBimoduleCoboundary L R n T = 0 := by
  rw [hochschildBimoduleCoboundary_compContinuousMultilinearMap f hL hR]
  constructor
  · intro h
    ext a
    apply hf
    simpa only [compContinuousMultilinearMap_coe, Function.comp_apply,
      _root_.zero_apply, map_zero] using congrArg (fun S ↦ S a) h
  · rintro h
    ext a
    simp only [h, compContinuousMultilinearMap_coe, Function.comp_apply,
      _root_.zero_apply, map_zero]

/-- A bounded bimodule inclusion with a bounded bimodule retraction preserves and reflects
actual Hochschild coboundaries, without taking a closure of their range. -/
theorem exists_hochschildBimoduleCoboundary_eq_comp_iff_of_leftInverse
    (f : E →L[𝕜] F) (g : F →L[𝕜] E)
    (hfL : ∀ a x, f (L a x) = L' a (f x))
    (hfR : ∀ a x, f (R a x) = R' a (f x))
    (hgL : ∀ a x, g (L' a x) = L a (g x))
    (hgR : ∀ a x, g (R' a x) = R a (g x))
    (hgf : Function.LeftInverse g f)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E) :
    (∃ S, hochschildBimoduleCoboundary L' R' n S = f.compContinuousMultilinearMap T) ↔
      ∃ S, hochschildBimoduleCoboundary L R n S = T := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨g.compContinuousMultilinearMap S, ?_⟩
    rw [hochschildBimoduleCoboundary_compContinuousMultilinearMap g hgL hgR, hS]
    ext a
    simpa only [compContinuousMultilinearMap_coe, Function.comp_apply] using hgf (T a)
  · rintro ⟨S, hS⟩
    exact ⟨f.compContinuousMultilinearMap S,
      (hochschildBimoduleCoboundary_compContinuousMultilinearMap f hfL hfR S).trans
        (congrArg f.compContinuousMultilinearMap hS)⟩

end ContinuousLinearMap
