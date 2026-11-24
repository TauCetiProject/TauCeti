/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.MayerVietoris

import Mathlib.Algebra.FiveLemma
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.DeRham.DisjointUnion
import TauCeti.Geometry.Manifold.DeRham.Euclidean
import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.DeRham.OrientationCover
import TauCeti.LinearAlgebra.Dual.Annihilator
import TauCeti.Topology.MayerVietoris

/-!
# De Rham Poincaré duality

On an oriented boundaryless Hausdorff σ-compact finite-dimensional smooth manifold `M` of dimension
`k + l`, with no compactness hypothesis, `TauCeti.poincarePairing` induces a linear isomorphism
`H^k_dR(M) ≃ₗ[ℝ] Module.Dual ℝ (H^l_c(M))` (`TauCeti.bijective_poincarePairing`,
`TauCeti.poincareDuality`), proved by `TauCeti.mayerVietoris_induction` from Euclidean open boxes,
Mayer–Vietoris connecting maps (`TauCeti.poincarePairing_mayerVietorisδ`), and disjoint open unions
(`TauCeti.bijective_poincarePairing_iSup`). Corollaries include nondegeneracy, compact-manifold
duality `TauCeti.poincareDualityCompact`, finite-dimensionality on compact manifolds (including
nonorientable ones via `Manifold.OrientationCover`), and Betti-number symmetry
(`TauCeti.finrank_deRhamCohomology_eq_of_orientation`).

## References
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17 and Problems 18-6 to 18-8.
* Raoul Bott and Loring W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Chapter I, §5.
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti

section MayerVietorisStep

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

private def prodPoincarePairing (U V : Opens M) [SigmaCompactSpace U] [SigmaCompactSpace V]
    {a b : ℕ} (o : Manifold.Orientation I M (Fin (a + b))) :
    (deRhamCohomology I U a × deRhamCohomology I V a) →ₗ[ℝ]
      Module.Dual ℝ
        (compactlySupportedDeRhamCohomology I U b × compactlySupportedDeRhamCohomology I V b) :=
  (Module.dualProdDualEquivDual ℝ _ _).toLinearMap.comp
    ((poincarePairing I U (o.restrict U)).prodMap (poincarePairing I V (o.restrict V)))

omit [SigmaCompactSpace M] in
private theorem bijective_prodPoincarePairing (U V : Opens M) [SigmaCompactSpace U]
    [SigmaCompactSpace V] {a b : ℕ} (o : Manifold.Orientation I M (Fin (a + b)))
    (hU : Bijective (poincarePairing I U (o.restrict U)))
    (hV : Bijective (poincarePairing I V (o.restrict V))) : Bijective (prodPoincarePairing U V o) :=
  (Module.dualProdDualEquivDual ℝ _ _).bijective.comp (hU.prodMap hV)

omit [SigmaCompactSpace M] in
private theorem comm_poincarePairing_sup_prod (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V] [SigmaCompactSpace (U ⊔ V : Opens M)]
    {a b : ℕ} (o : Manifold.Orientation I M (Fin (a + b))) :
    ((compactlySupportedDeRhamCohomology.extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V) b).coprod
        (compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (le_sup_right : V ≤ U ⊔ V) b)).dualMap.comp
      (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))) =
    (prodPoincarePairing U V o).comp
      ((deRhamCohomology.map (Opens.inclusion (le_sup_left : U ≤ U ⊔ V))
          (contMDiff_inclusion _) a).prod
        (deRhamCohomology.map (Opens.inclusion (le_sup_right : V ≤ U ⊔ V))
          (contMDiff_inclusion _) a)) :=
  LinearMap.ext fun _ ↦ LinearMap.ext fun ⟨_, _⟩ ↦ by
    simp [prodPoincarePairing, poincarePairing_extendByZero]

omit [SigmaCompactSpace M] in
private theorem comm_poincarePairing_prod_inf (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V] [SigmaCompactSpace (U ⊓ V : Opens M)]
    {a b : ℕ} (o : Manifold.Orientation I M (Fin (a + b))) :
    ((compactlySupportedDeRhamCohomology.extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U) b).prod
        (-compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (inf_le_right : U ⊓ V ≤ V) b)).dualMap.comp
      (prodPoincarePairing U V o) =
    (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V))).comp
      ((deRhamCohomology.map (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
          (contMDiff_inclusion _) a).coprod
        (-deRhamCohomology.map (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
          (contMDiff_inclusion _) a)) :=
  LinearMap.ext fun ⟨_, _⟩ ↦ LinearMap.ext fun _ ↦ by
    simp [prodPoincarePairing, poincarePairing_extendByZero]

/-- Degree-zero step of the Mayer–Vietoris union argument for Poincaré duality on `U ⊔ V`. -/
private theorem bijective_poincarePairing_sup_zero {b : ℕ}
    (o : Manifold.Orientation I M (Fin (0 + b))) (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    (hU : Bijective (poincarePairing I U (o.restrict U)))
    (hV : Bijective (poincarePairing I V (o.restrict V)))
    (hUV : Injective (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)))) :
    Bijective (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))) := by
  -- Above the manifold dimension `b = dim M`, `H_c^{b+1}(U ⊓ V) = 0`, so extension by zero
  -- `H_c^b(U) × H_c^b(V) → H_c^b(U ⊔ V)` is surjective and its dual map is injective.
  have hl : Module.finrank ℝ E < b + 1 := by
    have hcard := o.card_eq; rw [Fintype.card_fin] at hcard; omega
  have := subsingleton_compactlySupportedDeRhamCohomology_of_finrank_lt I (U ⊓ V : Opens M) hl
  have hsurj : Surjective
      ((compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (le_sup_left : U ≤ U ⊔ V) b).coprod
        (compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (le_sup_right : V ≤ U ⊔ V) b)) := fun y ↦
    (compactlySupportedDeRhamCohomology.exact_mayerVietoris₃ U V b y).mp (Subsingleton.elim _ 0)
  -- Apply the left-exact three-term lemma to:
  --   0 ─▶ H⁰(U ⊔ V) ──▶ H⁰(U) × H⁰(V) ──────▶ H⁰(U ⊓ V)
  --           │                 │                   │
  --        P_{U ⊔ V}         P_{U, V}            P_{U ⊓ V}
  --           ▼                 ▼                   ▼
  --   0 ─▶ H_c^b(U ⊔ V)* ─▶ (H_c^b(U) × H_c^b(V))* ─▶ H_c^b(U ⊓ V)*
  exact LinearMap.bijective_of_bijective_of_injective_of_left_exact _ _ _ _
    (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))) (prodPoincarePairing U V o)
    (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)))
    (comm_poincarePairing_sup_prod U V o) (comm_poincarePairing_prod_inf U V o)
    (deRhamCohomology.exact_mayerVietoris₂ U V 0)
    (LinearMap.exact_dualMap_iff.mpr
      (compactlySupportedDeRhamCohomology.exact_mayerVietoris₂ U V b))
    (bijective_prodPoincarePairing U V o hU hV) hUV
    (deRhamCohomology.injective_mayerVietoris_zero U V)
    (LinearMap.dualMap_injective_of_surjective hsurj)

/-- Positive-degree step of the Mayer–Vietoris union argument for Poincaré duality on `U ⊔ V`,
applying the five lemma to the signed pairing diagram connecting degrees `(j, b + 1)` and
`(j + 1, b)`. -/
private theorem bijective_poincarePairing_sup_succ {j b : ℕ}
    (o : Manifold.Orientation I M (Fin (j + 1 + b)))
    (U V : Opens M) [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    (hU' : Bijective (poincarePairing (k := j) (l := b + 1) I U
      ((o.reindex (finCongr (add_right_comm j 1 b))).restrict U)))
    (hV' : Bijective (poincarePairing (k := j) (l := b + 1) I V
      ((o.reindex (finCongr (add_right_comm j 1 b))).restrict V)))
    (hUV' : Bijective (poincarePairing (k := j) (l := b + 1) I (U ⊓ V : Opens M)
      ((o.reindex (finCongr (add_right_comm j 1 b))).restrict (U ⊓ V))))
    (hU : Bijective (poincarePairing (k := j + 1) (l := b) I U (o.restrict U)))
    (hV : Bijective (poincarePairing (k := j + 1) (l := b) I V (o.restrict V)))
    (hUV : Injective (poincarePairing (k := j + 1) (l := b) I (U ⊓ V : Opens M)
      (o.restrict (U ⊓ V)))) :
    Bijective (poincarePairing (k := j + 1) (l := b) I (U ⊔ V : Opens M)
      (o.restrict (U ⊔ V))) := by
  let o' := o.reindex (finCongr (add_right_comm j 1 b))
  -- `poincarePairing_mayerVietorisδ` satisfies `P_{U ⊔ V} (δ x) y = s * P_{U ⊓ V} x (δ_c y)`
  -- with the unit sign factor `s = (-1)^(j + 1)`. Multiplying the first two vertical pairings
  -- (at degree `(j, b + 1)`) by `s` makes all four squares of the five-term diagram commute
  -- strictly. Writing `(H_c^q)₂ := H_c^q(U) × H_c^q(V)`, the diagram is:
  --
  --   H^j(U)×H^j(V) ─▶ H^j(U⊓V) ─δ─▶ H^{j+1}(U⊔V) ─▶ H^{j+1}(U)×H^{j+1}(V) ─▶ H^{j+1}(U⊓V)
  --         │             │               │                    │                    │
  --     s•P_{U,V}     s•P_{U⊓V}        P_{U⊔V}              P_{U,V}              P_{U⊓V}
  --         ▼             ▼               ▼                    ▼                    ▼
  --   (H_c^{b+1})₂* ─▶ H_c^{b+1}(U⊓V)* ─δ_c*─▶ H_c^b(U⊔V)* ─▶ (H_c^b)₂* ─▶ H_c^b(U⊓V)*
  let s : ℝ := (-1 : ℝ) ^ (j + 1)
  have hs : IsUnit s := isUnit_one.neg.pow (j + 1)
  have hsmul {A B : Type _} [AddCommMonoid A] [Module ℝ A] [AddCommMonoid B] [Module ℝ B]
      {f : A →ₗ[ℝ] B} (hf : Bijective f) : Bijective (s • f) := by
    have heq : ⇑(s • f) = (s • ·) ∘ ⇑f := funext (LinearMap.smul_apply s f)
    rw [heq]
    exact hs.smul_bijective.comp hf
  have hc₁ : ((compactlySupportedDeRhamCohomology.extendByZero (I := I)
        (inf_le_left : U ⊓ V ≤ U) (b + 1)).prod
        (-compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (inf_le_right : U ⊓ V ≤ V) (b + 1))).dualMap.comp
      (s • prodPoincarePairing (a := j) (b := b + 1) U V o') =
      (s • poincarePairing (k := j) (l := b + 1) I (U ⊓ V : Opens M) (o'.restrict (U ⊓ V))).comp
        ((deRhamCohomology.map (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
            (contMDiff_inclusion _) j).coprod
          (-deRhamCohomology.map (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
            (contMDiff_inclusion _) j)) := by
    rw [LinearMap.comp_smul, LinearMap.smul_comp,
      comm_poincarePairing_prod_inf (a := j) (b := b + 1) U V o']
  have hc₂ : (compactlySupportedDeRhamCohomology.mayerVietorisδ I U V b).dualMap.comp
      (s • poincarePairing (k := j) (l := b + 1) I (U ⊓ V : Opens M) (o'.restrict (U ⊓ V))) =
      (poincarePairing (k := j + 1) (l := b) I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))).comp
        (deRhamCohomology.mayerVietorisδ I U V j) :=
    LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ by
      simpa only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearMap.smul_apply,
        smul_eq_mul, s, o'] using (poincarePairing_mayerVietorisδ o x y).symm
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective _ _ _ _ _ _ _ _
    (s • prodPoincarePairing (a := j) (b := b + 1) U V o')
    (s • poincarePairing (k := j) (l := b + 1) I (U ⊓ V : Opens M) (o'.restrict _))
    (poincarePairing (k := j + 1) (l := b) I (U ⊔ V : Opens M) (o.restrict (U ⊔ V)))
    (prodPoincarePairing (a := j + 1) (b := b) U V o)
    (poincarePairing (k := j + 1) (l := b) I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)))
    hc₁ hc₂ (comm_poincarePairing_sup_prod (a := j + 1) (b := b) U V o)
    (comm_poincarePairing_prod_inf (a := j + 1) (b := b) U V o)
    (deRhamCohomology.exact_mayerVietoris₃ U V j) (deRhamCohomology.exact_mayerVietoris₁ U V j)
    (deRhamCohomology.exact_mayerVietoris₂ U V (j + 1))
    (LinearMap.exact_dualMap_iff.mpr
      (compactlySupportedDeRhamCohomology.exact_mayerVietoris₁ U V b))
    (LinearMap.exact_dualMap_iff.mpr
      (compactlySupportedDeRhamCohomology.exact_mayerVietoris₃ U V b))
    (LinearMap.exact_dualMap_iff.mpr
      (compactlySupportedDeRhamCohomology.exact_mayerVietoris₂ U V b))
    (hsmul (bijective_prodPoincarePairing (a := j) (b := b + 1) U V o' hU' hV')).surjective
    (hsmul hUV') (bijective_prodPoincarePairing (a := j + 1) (b := b) U V o hU hV) hUV

private theorem bijective_poincarePairing_sup {n : ℕ} (o : Manifold.Orientation I M (Fin n))
    (U V : Opens M) [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    (hU : ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I U ((o.reindex (finCongr hab.symm)).restrict U)))
    (hV : ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I V ((o.reindex (finCongr hab.symm)).restrict V)))
    (hUV : ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I (U ⊓ V : Opens M)
        ((o.reindex (finCongr hab.symm)).restrict (U ⊓ V)))) :
    ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I (U ⊔ V : Opens M)
        ((o.reindex (finCongr hab.symm)).restrict (U ⊔ V))) := by
  intro a b hab
  cases a with
  | zero =>
    exact bijective_poincarePairing_sup_zero (o.reindex (finCongr hab.symm)) U V
      (hU 0 b hab) (hV 0 b hab) (hUV 0 b hab).injective
  | succ j =>
    have hjb : j + (b + 1) = n := by omega
    have hre : (o.reindex (finCongr hab.symm)).reindex (finCongr (add_right_comm j 1 b)) =
        o.reindex (finCongr hjb.symm) :=
      Manifold.Orientation.reindex_finCongr_reindex_finCongr _ _ o
    exact bijective_poincarePairing_sup_succ (o.reindex (finCongr hab.symm)) U V
      (hre.symm ▸ hU j (b + 1) hjb) (hre.symm ▸ hV j (b + 1) hjb)
      (hre.symm ▸ hUV j (b + 1) hjb)
      (hU (j + 1) b hab) (hV (j + 1) b hab) (hUV (j + 1) b hab).injective

end MayerVietorisStep

section BaseAndGlobalization

section DualityTransport

variable {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [BoundarylessManifold J N] [T2Space N] [SigmaCompactSpace N] {k l : ℕ}

private theorem bijective_poincarePairing_of_isEmpty [IsEmpty M]
    (o : Manifold.Orientation I M (Fin (k + l))) : Bijective (poincarePairing I M o) := by
  have : Subsingleton (SmoothForm I M ℝ k) :=
    ⟨fun _ _ ↦ Subtype.ext (funext fun x ↦ isEmptyElim x)⟩
  have : Subsingleton (deRhamCohomology I M k) := (deRhamCohomology.mk_surjective I k).subsingleton
  have : Subsingleton (SmoothForm I M ℝ l) :=
    ⟨fun _ _ ↦ Subtype.ext (funext fun x ↦ isEmptyElim x)⟩
  have : Subsingleton (compactlySupportedDeRhamCohomology I M l) :=
    (compactlySupportedDeRhamCohomology.mk_surjective I l).subsingleton
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

private theorem bijective_poincarePairing_iff_of_isOrientationPreserving
    (Φ : M ≃ₘ⟮I, J⟯ N) (o : Manifold.Orientation I M (Fin (k + l)))
    (o' : Manifold.Orientation J N (Fin (k + l)))
    (hpres : ∀ x : M, o.IsOrientationPreservingAt o' Φ x) :
    Bijective (poincarePairing I M o) ↔ Bijective (poincarePairing J N o') := by
  let e₁ := deRhamCohomology.equivOfDiffeomorph Φ k
  let e₂ := compactlySupportedDeRhamCohomology.equivOfDiffeomorph Φ l
  have hfn : ⇑(poincarePairing J N o') = ⇑e₂.dualMap ∘ ⇑(poincarePairing I M o) ∘ ⇑e₁ :=
    funext fun x ↦ LinearMap.ext fun y ↦ by
      simpa only [Function.comp_apply, LinearEquiv.dualMap_apply, e₁, e₂,
        deRhamCohomology.equivOfDiffeomorph_apply,
        compactlySupportedDeRhamCohomology.equivOfDiffeomorph_apply] using
        (poincarePairing_map_diffeomorph o o' Φ hpres x y).symm
  rw [hfn, e₂.dualMap.bijective.of_comp_iff', Bijective.of_comp_iff _ e₁.bijective]

private theorem bijective_poincarePairing_of_diffeomorph
    (Φ : M ≃ₘ⟮I, J⟯ N) (o : Manifold.Orientation I M (Fin (k + l)))
    (hN : ∀ o' : Manifold.Orientation J N (Fin (k + l)), Bijective (poincarePairing J N o')) :
    Bijective (poincarePairing I M o) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact bijective_poincarePairing_of_isEmpty o
  · have hdim : Fintype.card (Fin (k + l)) = Module.finrank ℝ E' :=
      o.card_eq.trans (Φ.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv.finrank_eq
    let o' := o.pullback (Φ.symm.contMDiff.of_le (by simp))
      (fun _ ↦ Φ.symm.isInvertible_mfderiv (by simp)) hdim
    exact (bijective_poincarePairing_iff_of_isOrientationPreserving Φ.symm o' o
      (Manifold.Orientation.isOrientationPreservingAt_pullback _ _ _ _)).mp (hN o')

end DualityTransport

/-- **Poincaré duality on a finite-dimensional real normed space.** -/
theorem bijective_poincarePairing_normedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {k l : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin (k + l))) :
    Bijective (poincarePairing 𝓘(ℝ, E) E o) := by
  have hdim : k + l = Module.finrank ℝ E := by simpa only [Fintype.card_fin] using o.card_eq
  cases k with
  | zero =>
    have hconst : Bijective (deRhamCohomology.const 𝓘(ℝ, E) E) :=
      ⟨deRhamCohomology.const_injective, fun c ↦
        let ⟨r, hr⟩ := deRhamCohomology.exists_eq_const c; ⟨r, hr.symm⟩⟩
    let eI := LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.bijective_integral (o.reindex (finCongr (zero_add l))))
    let eR : ℝ ≃ₗ[ℝ] Module.Dual ℝ ℝ := (LinearMap.ringLmapEquivSelf ℝ ℝ ℝ).symm
    have hcomm : (poincarePairing 𝓘(ℝ, E) E o).comp (deRhamCohomology.const 𝓘(ℝ, E) E) =
        eI.dualMap.toLinearMap.comp eR.toLinearMap :=
      LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ by simp [eI, eR, mul_comm]
    refine (Bijective.of_comp_iff (poincarePairing 𝓘(ℝ, E) E o) hconst).mp ?_
    rw [← LinearMap.coe_comp, hcomm, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap,
      LinearEquiv.coe_toLinearMap]
    exact eI.dualMap.bijective.comp eR.bijective
  | succ j =>
    have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) E (j + 1)) :=
      subsingleton_deRhamCohomology_normedSpace (E := E) j
    have : Subsingleton (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E l) :=
      subsingleton_compactlySupportedDeRhamCohomology_normedSpace E (by omega)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

private theorem bijective_poincarePairing_opens_of_isBasis
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [SecondCountableTopology M] [LocallyCompactSpace M] {n : ℕ}
    (o : Manifold.Orientation I M (Fin n)) (B : Set (Opens M)) (hB : Opens.IsBasis B)
    (hinf : ∀ U ∈ B, ∀ V ∈ B, ((U ⊓ V : Opens M) : Set M).Nonempty → U ⊓ V ∈ B)
    (hbase : ∀ U ∈ B, (U : Set M).Nonempty → ∀ [SigmaCompactSpace U] (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I U ((o.reindex (finCongr hab.symm)).restrict U)))
    (W : Opens M) [SigmaCompactSpace W] :
    ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I W ((o.reindex (finCongr hab.symm)).restrict W)) := by
  let P (U : Opens M) : Prop :=
    ∀ [SigmaCompactSpace U] (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I U ((o.reindex (finCongr hab.symm)).restrict U))
  exact mayerVietoris_induction P B hB hinf
    (by
      intro _ a b hab; have : IsEmpty (⊥ : Opens M) := isEmpty_coe_sort.mpr rfl
      exact bijective_poincarePairing_of_isEmpty _)
    hbase
    (fun U V hU hV hUV _ a b hab ↦ bijective_poincarePairing_sup o U V hU hV hUV a b hab)
    (fun s hs hPs _ a b hab ↦
      bijective_poincarePairing_iSup (o.reindex (finCongr hab.symm)) hs
        fun m ↦ hPs m a b hab) W

private theorem bijective_poincarePairing_opens_euclideanSpace {d n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) (Fin n))
    (W : Opens (EuclideanSpace ℝ (Fin d))) [SigmaCompactSpace W] :
    ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) W
        ((o.reindex (finCongr hab.symm)).restrict W)) :=
  bijective_poincarePairing_opens_of_isBasis o _ (isBasis_openBoxes (Fin d))
    (by
      rintro _ ⟨a₁, b₁, rfl⟩ _ ⟨a₂, b₂, rfl⟩ _
      exact ⟨_, _, openBox_inf_openBox a₁ b₁ a₂ b₂⟩)
    (by
      rintro U ⟨p, q, rfl⟩ hne _ a b hab
      exact bijective_poincarePairing_of_diffeomorph
        (diffeomorphOpenBox (n := ⊤) (nonempty_openBox_iff.mp hne.to_subtype)).symm _
        fun o' ↦ bijective_poincarePairing_normedSpace _ o') W

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

private theorem bijective_poincarePairing_of_le_diffeomorph_euclideanSpace
    [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    {U W : Opens M} [SigmaCompactSpace W] (hWU : W ≤ U)
    (Φ : U ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    {a b : ℕ} (oM : Manifold.Orientation I M (Fin (a + b))) :
    Bijective (poincarePairing I W (oM.restrict W)) := by
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  let V : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ⟨{z | (Φ.symm z : M) ∈ W}, W.isOpen.preimage (continuous_subtypeVal.comp Φ.symm.continuous)⟩
  have : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  let Ψ : W ≃ₘ⟮I, J⟯ V :=
    { toEquiv :=
        { toFun := fun w ↦ ⟨Φ ⟨w.val, hWU w.property⟩, by simp [V, Φ.symm_apply_apply]⟩
          invFun := fun v ↦ ⟨(Φ.symm v.val).val, v.property⟩
          left_inv := fun w ↦ Subtype.ext <| by
            dsimp only; exact congrArg Subtype.val (Φ.symm_apply_apply ⟨w.val, hWU w.property⟩)
          right_inv := fun v ↦ Subtype.ext (Φ.apply_symm_apply v.val) }
      contMDiff_toFun :=
        (ContMDiff.subtypeVal_comp_iff _ _).mp (Φ.contMDiff.comp (contMDiff_inclusion hWU))
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
        ((contMDiff_subtypeVal (I := I) (U := U)).comp
          (Φ.symm.contMDiff.comp contMDiff_subtypeVal)) }
  let oE : Manifold.Orientation J (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (Fin (a + b)) :=
    (oM.restrict U).pullback (Φ.symm.contMDiff.of_le (by simp))
      (fun _ ↦ Φ.symm.isInvertible_mfderiv (by simp))
      (oM.card_eq.trans (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := Module.finrank ℝ E)).symm)
  have hΨ_pres (w : W) : (oM.restrict W).IsOrientationPreservingAt (oE.restrict V) Ψ w := by
    have hcomp : ((Subtype.val : U → M) ∘ Φ.symm ∘ (Subtype.val : V → _)) ∘ Ψ =
        (Subtype.val : W → M) :=
      funext fun z ↦ congrArg Subtype.val (Φ.symm_apply_apply ⟨z.val, hWU z.property⟩)
    exact ((oM.isOrientationPreservingAt_restrict U _).comp
      ((Manifold.Orientation.isOrientationPreservingAt_pullback _ _ _ _ _).comp
        (oE.isOrientationPreservingAt_restrict V (Ψ w)))).of_comp
      (hcomp.symm ▸ oM.isOrientationPreservingAt_restrict W w)
      (Ψ.contMDiff.mdifferentiableAt (by simp))
  refine (bijective_poincarePairing_iff_of_isOrientationPreserving Ψ _ _ hΨ_pres).mpr ?_
  simpa only [finCongr_refl, Manifold.Orientation.reindex_refl] using
    bijective_poincarePairing_opens_euclideanSpace oE V a b rfl

/-- **De Rham Poincaré duality.** On an oriented boundaryless Hausdorff σ-compact finite-dimensional
smooth manifold `M` of dimension `k + l`, with no compactness hypothesis, the Poincaré pairing
`TauCeti.poincarePairing I M o` is a bijection from `H^k_dR(M)` onto the dual of `H^l_c(M)`. -/
theorem bijective_poincarePairing [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l))) :
    Function.Bijective (poincarePairing I M o : deRhamCohomology I M k →
      Module.Dual ℝ (compactlySupportedDeRhamCohomology I M l)) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  choose U hxU hΦ using fun x : M ↦
    exists_opens_diffeomorph_euclideanSpace (n := ⊤)
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  have htop_kl : Bijective (poincarePairing I (⊤ : Opens M) (o.restrict ⊤)) := by
    simpa only [finCongr_refl, Manifold.Orientation.reindex_refl] using
      bijective_poincarePairing_opens_of_isBasis o {W : Opens M | ∃ x : M, W ≤ U x}
        (Opens.isBasis_iff_nbhd.mpr fun {W x} hxW ↦
          ⟨W ⊓ U x, ⟨x, inf_le_right⟩, ⟨hxW, hxU x⟩, inf_le_left⟩)
        (fun _ ⟨x, hx⟩ _ _ _ ↦ ⟨x, inf_le_left.trans hx⟩)
        (fun _ ⟨x, hW⟩ _ _ _ _ hab ↦
          bijective_poincarePairing_of_le_diffeomorph_euclideanSpace hW (hΦ x).some
            (o.reindex (finCongr hab.symm))) ⊤ k l rfl
  let Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop ⊤ rfl
  exact (bijective_poincarePairing_iff_of_isOrientationPreserving Φ _ _ fun z ↦ by
    rw [Diffeomorph.coe_ofTop]; exact o.isOrientationPreservingAt_restrict ⊤ z).mp htop_kl

end BaseAndGlobalization

section BundledAPI

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] {k l : ℕ}

/-- **De Rham Poincaré duality** as a linear equivalence `H^k_dR(M) ≃ₗ[ℝ] (H^l_c(M))^*`. -/
def poincareDuality (o : Manifold.Orientation I M (Fin (k + l))) :
    deRhamCohomology I M k ≃ₗ[ℝ] Module.Dual ℝ (compactlySupportedDeRhamCohomology I M l) :=
  LinearEquiv.ofBijective (poincarePairing I M o) (bijective_poincarePairing o)

/-- `TauCeti.poincareDuality` evaluates as `TauCeti.poincarePairing`. -/
@[simp]
theorem poincareDuality_apply (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M k) (y : compactlySupportedDeRhamCohomology I M l) :
    poincareDuality o x y = poincarePairing I M o x y := (rfl)

/-- The underlying linear map of `TauCeti.poincareDuality` is `TauCeti.poincarePairing`. -/
@[simp]
theorem poincareDuality_toLinearMap (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincareDuality o).toLinearMap = poincarePairing I M o := (rfl)

/-- Reversing the orientation negates `TauCeti.poincareDuality`. -/
@[simp]
theorem poincareDuality_neg (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M k) :
    poincareDuality (-o) x = -poincareDuality o x := by ext y; simp [poincareDuality_apply]

/-- The Poincaré pairing is left-separating. -/
theorem poincarePairing_separatingLeft (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincarePairing I M o).SeparatingLeft :=
  LinearMap.separatingLeft_iff_ker_eq_bot.mpr
    (LinearMap.ker_eq_bot_of_injective (bijective_poincarePairing o).injective)

/-- The Poincaré pairing is right-separating. -/
theorem poincarePairing_separatingRight (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincarePairing I M o).SeparatingRight := fun y hy ↦
  (Module.forall_dual_apply_eq_zero_iff ℝ y).mp fun φ ↦
    let ⟨x, hx⟩ := (bijective_poincarePairing o).surjective φ; hx ▸ hy x

/-- **Nondegeneracy of the Poincaré pairing** in both arguments. -/
theorem poincarePairing_nondegenerate (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincarePairing I M o).Nondegenerate :=
  ⟨poincarePairing_separatingLeft o, poincarePairing_separatingRight o⟩

/-- If `x ∈ H^k_dR(M)` pairs to zero with every `y ∈ H^l_c(M)`, then `x = 0`. -/
theorem eq_zero_of_forall_poincarePairing_eq_zero_left
    (o : Manifold.Orientation I M (Fin (k + l))) {x : deRhamCohomology I M k}
    (hx : ∀ y, poincarePairing I M o x y = 0) : x = 0 := poincarePairing_separatingLeft o x hx

/-- If every `x ∈ H^k_dR(M)` pairs to zero with `y ∈ H^l_c(M)`, then `y = 0`. -/
theorem eq_zero_of_forall_poincarePairing_eq_zero_right
    (o : Manifold.Orientation I M (Fin (k + l))) {y : compactlySupportedDeRhamCohomology I M l}
    (hy : ∀ x, poincarePairing I M o x y = 0) : y = 0 := poincarePairing_separatingRight o y hy

end BundledAPI

section CompactManifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

/-- On a compact oriented boundaryless manifold of dimension `k + l`, Poincaré duality identifies
`H^k_dR(M)` with the dual of `H^l_dR(M)`. -/
def poincareDualityCompact {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l))) :
    deRhamCohomology I M k ≃ₗ[ℝ] Module.Dual ℝ (deRhamCohomology I M l) :=
  (poincareDuality o).trans (LinearEquiv.ofBijective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I l)).symm.dualMap

/-- `TauCeti.poincareDualityCompact` agrees with `TauCeti.poincarePairing` on classes coming from
compactly supported cohomology. -/
@[simp]
theorem poincareDualityCompact_apply_toDeRhamCohomology {k l : ℕ}
    (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M k) (y : compactlySupportedDeRhamCohomology I M l) :
    poincareDualityCompact o x
        (compactlySupportedDeRhamCohomology.toDeRhamCohomology I M l y) =
      poincarePairing I M o x y := by
  rw [poincareDualityCompact, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    LinearEquiv.ofBijective_symm_apply_apply, poincareDuality_apply]

/-- Reversing the orientation negates `TauCeti.poincareDualityCompact`. -/
@[simp]
theorem poincareDualityCompact_neg {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M k) :
    poincareDualityCompact (-o) x = -poincareDualityCompact o x := by
  ext z
  obtain ⟨y, rfl⟩ :=
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I l).surjective z
  simp

private theorem finiteDimensional_deRhamCohomology_of_orientation
    (o : Manifold.Orientation I M (Fin (Module.finrank ℝ E))) (k : ℕ) :
    FiniteDimensional ℝ (deRhamCohomology I M k) := by
  by_cases hk : k ≤ Module.finrank ℝ E
  · set l := Module.finrank ℝ E - k
    have hkl : k + l = Module.finrank ℝ E := Nat.add_sub_of_le hk
    have hlk : l + k = Module.finrank ℝ E := Nat.add_comm k l ▸ hkl
    let e₁ := poincareDualityCompact (o.reindex (finCongr hkl.symm))
    let e₂ := poincareDualityCompact (o.reindex (finCongr hlk.symm))
    rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
    by_contra! hinf
    have h₁ : Module.rank ℝ (deRhamCohomology I M k) <
        Module.rank ℝ (Module.Dual ℝ (deRhamCohomology I M k)) := by
      simpa only [Cardinal.lift_id'] using lift_rank_lt_rank_dual hinf
    have h₂ : Module.rank ℝ (deRhamCohomology I M l) <
        Module.rank ℝ (Module.Dual ℝ (deRhamCohomology I M l)) := by
      simpa only [Cardinal.lift_id'] using
        lift_rank_lt_rank_dual (hinf.trans (h₁.le.trans_eq e₂.symm.rank_eq))
    exact lt_irrefl _ ((h₁.trans_eq e₂.symm.rank_eq).trans (h₂.trans_eq e₁.symm.rank_eq))
  · push Not at hk
    have := subsingleton_deRhamCohomology_of_finrank_lt I M hk
    infer_instance

/-- **Finite-dimensionality of de Rham cohomology on a compact boundaryless manifold** (orientable
or nonorientable, via injective pullback to `Manifold.OrientationCover`). -/
instance finiteDimensional_deRhamCohomology (k : ℕ) :
    FiniteDimensional ℝ (deRhamCohomology I M k) := by
  have : CompactSpace (Manifold.OrientationCover I M) :=
    ⟨by simpa only [preimage_univ] using
      (Manifold.OrientationCover.isProperMap_proj I M).isCompact_preimage isCompact_univ⟩
  have : FiniteDimensional ℝ (deRhamCohomology I (Manifold.OrientationCover I M) k) :=
    finiteDimensional_deRhamCohomology_of_orientation
      Manifold.OrientationCover.canonicalOrientation k
  exact FiniteDimensional.of_injective _
    (Manifold.OrientationCover.deRhamCohomology_map_proj_injective k)

/-- Compactly supported de Rham cohomology of a compact boundaryless manifold is
finite-dimensional. -/
instance finiteDimensional_compactlySupportedDeRhamCohomology (k : ℕ) :
    FiniteDimensional ℝ (compactlySupportedDeRhamCohomology I M k) :=
  FiniteDimensional.of_injective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I k).injective

/-- **Betti-number symmetry on a compact oriented boundaryless manifold.** -/
theorem finrank_deRhamCohomology_eq_of_orientation {k l : ℕ}
    (o : Manifold.Orientation I M (Fin (k + l))) :
    Module.finrank ℝ (deRhamCohomology I M k) = Module.finrank ℝ (deRhamCohomology I M l) :=
  (poincareDualityCompact o).finrank_eq.trans Subspace.dual_finrank_eq

end CompactManifold

end TauCeti
