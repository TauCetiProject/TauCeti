/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Intertwining operators through the continuous functional calculus

Let `X : E →L[𝕜] F` be a bounded operator between Hilbert spaces which intertwines operators
`a` on `E` and `b` on `F`, in the sense that `X a = b X`, and which also intertwines their
adjoints. Then `X` intertwines every continuous function of `a` and `b`:

`X (f a) = (f b) X`.

Both `a` and `b` are evaluated on the compact set `spectrum a ∪ spectrum b`, where the
symbols satisfying this identity form a closed subalgebra containing the identity and its
conjugate. By the Stone–Weierstrass theorem this subalgebra is everything. This is the
two-space form of Mathlib's `Commute.cfc`, and the proof follows that of `Commute.cfcHom`.

For unitary operators the adjoint hypothesis is automatic, since the adjoint is the inverse.
For normal operators it is the content of the Fuglede–Putnam–Rosenblum theorem, which Mathlib
proves as `SemiconjBy.star_right` for elements of a single C⋆-algebra.

## Main results

* `ContinuousLinearMap.comp_cfc_eq_cfc_comp`: an operator intertwining `a, b` and their adjoints
  intertwines `cfc f a` and `cfc f b`.
* `ContinuousLinearMap.comp_star_eq_star_comp_of_mem_unitary`: an operator intertwining two
  unitaries intertwines their adjoints.

## References

* B. Fuglede, *A commutativity theorem for normal operators*, Proc. Nat. Acad. Sci. U.S.A. 36
  (1950), 35–40.
* C. R. Putnam, *On normal operators in Hilbert space*, Amer. J. Math. 73 (1951), 357–362.
-/

public section

open ContinuousMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Intertwining through the continuous functional calculus.** If `X` intertwines `a` and `b`
and also their adjoints, then it intertwines `cfc f a` and `cfc f b` for every symbol `f`
continuous on both spectra. -/
theorem comp_cfc_eq_cfc_comp {p : (E →L[𝕜] E) → Prop} {q : (F →L[𝕜] F) → Prop}
    [ContinuousFunctionalCalculus 𝕜 (E →L[𝕜] E) p]
    [ContinuousFunctionalCalculus 𝕜 (F →L[𝕜] F) q]
    (X : E →L[𝕜] F) {a : E →L[𝕜] E} {b : F →L[𝕜] F}
    (h : X ∘L a = b ∘L X) (h_star : X ∘L star a = star b ∘L X) (f : 𝕜 → 𝕜)
    (hfa : ContinuousOn f (spectrum 𝕜 a) := by cfc_cont_tac)
    (hfb : ContinuousOn f (spectrum 𝕜 b) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) (hb : q b := by cfc_tac) :
    X ∘L cfc f a = cfc f b ∘L X := by
  -- Both calculi are read on continuous symbols on the common compact set `K`.
  set K := spectrum 𝕜 a ∪ spectrum 𝕜 b
  have hca := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) (p := p) a
  have hcb := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) (p := q) b
  have : CompactSpace K := isCompact_iff_compactSpace.mp (hca.union hcb)
  let ιa : C(spectrum 𝕜 a, K) := ⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩
  let ιb : C(spectrum 𝕜 b, K) := ⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩
  let φa := (cfcHom ha).comp (ιa.compStarAlgHom' 𝕜 𝕜)
  let φb := (cfcHom hb).comp (ιb.compStarAlgHom' 𝕜 𝕜)
  have hφa : Continuous φa := (cfcHom_continuous ha).comp (continuous_precomp ιa)
  have hφb : Continuous φb := (cfcHom_continuous hb).comp (continuous_precomp ιb)
  have hφa_id : φa (.restrict K (.id 𝕜)) = a := by
    rw [← cfcHom_id (R := 𝕜) ha]
    exact congrArg (cfcHom ha) (ContinuousMap.ext fun _ => rfl)
  have hφb_id : φb (.restrict K (.id 𝕜)) = b := by
    rw [← cfcHom_id (R := 𝕜) hb]
    exact congrArg (cfcHom hb) (ContinuousMap.ext fun _ => rfl)
  -- The symbols on `K` intertwined by `X` contain the constants, the identity and its conjugate,
  -- and are closed under sums, products and limits, so by Stone–Weierstrass they are all symbols.
  have key (g : C(K, 𝕜)) : X ∘L φa g = φb g ∘L X := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      have hr : ContinuousMap.const K r = algebraMap 𝕜 C(K, 𝕜) r := by ext; simp
      rw [hr, AlgHomClass.commutes, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, comp_smul, smul_comp]
      simp only [one_def, comp_id, id_comp]
    | id => rwa [hφa_id, hφb_id]
    | star_id => rwa [map_star, map_star, hφa_id, hφb_id]
    | add f g hf hg => rw [map_add, map_add, comp_add, add_comp, hf, hg]
    | mul f g hf hg =>
      rw [map_mul, map_mul, mul_def, mul_def, ← comp_assoc, hf, comp_assoc, hg, comp_assoc]
    | frequently g hg =>
      have hclosed : IsClosed {g : C(K, 𝕜) | X ∘L φa g = φb g ∘L X} :=
        isClosed_eq ((compL 𝕜 E E F X).continuous.comp hφa)
          (((compL 𝕜 E F F).flip X).continuous.comp hφb)
      exact hclosed.closure_subset_iff.mpr subset_rfl
        (mem_closure_iff_frequently.mpr hg)
  -- `cfc f a` and `cfc f b` are the two calculi at the restriction of `f` to `K`.
  have hf : ContinuousOn f K :=
    hfa.union_of_isClosed hfb hca.isClosed hcb.isClosed
  have hfa' : cfc f a = φa ⟨_, hf.domRestrict⟩ := by
    rw [cfc_apply f a]
    exact congrArg (cfcHom ha) (ContinuousMap.ext fun _ => rfl)
  have hfb' : cfc f b = φb ⟨_, hf.domRestrict⟩ := by
    rw [cfc_apply f b]
    exact congrArg (cfcHom hb) (ContinuousMap.ext fun _ => rfl)
  rw [hfa', hfb', key]

/-- An operator intertwining two unitaries also intertwines their adjoints, which are their
inverses. -/
theorem comp_star_eq_star_comp_of_mem_unitary (X : E →L[𝕜] F) {u : E →L[𝕜] E} {v : F →L[𝕜] F}
    (hu : u ∈ unitary (E →L[𝕜] E)) (hv : v ∈ unitary (F →L[𝕜] F)) (h : X ∘L u = v ∘L X) :
    X ∘L star u = star v ∘L X := by
  have hu' : X ∘L (u * star u) = X := by rw [Unitary.mul_star_self_of_mem hu, one_def, comp_id]
  have hv' : (star v * v) ∘L X = X := by rw [Unitary.star_mul_self_of_mem hv, one_def, id_comp]
  calc X ∘L star u = (star v * v) ∘L X ∘L star u := by rw [← comp_assoc, hv']
    _ = star v ∘L X ∘L (u * star u) := by
        rw [mul_def, mul_def, comp_assoc, ← comp_assoc v, ← h, comp_assoc]
    _ = star v ∘L X := by rw [hu']

end ContinuousLinearMap
