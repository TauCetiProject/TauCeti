/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic
public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.DeRham.CompactlySupportedMayerVietoris
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OpenSubset
import TauCeti.LinearAlgebra.Exact
import Mathlib.Algebra.FiveLemma
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The Poincaré pairing and the Mayer–Vietoris sequences

Let `M` be an oriented boundaryless manifold of dimension `n`, and let `U` and `V` be open
subsets. The Poincaré pairing `⟨[φ], [ψ]⟩ = ∫ φ ∧ ψ` between de Rham cohomology and compactly
supported de Rham cohomology (`TauCeti.poincarePairing`) intertwines the Mayer–Vietoris sequence of
de Rham cohomology,

`⋯ → H^k(U ⊔ V) → H^k(U) ⊕ H^k(V) → H^k(U ⊓ V) → H^{k+1}(U ⊔ V) → ⋯`,

with the dual of the Mayer–Vietoris sequence of compactly supported cohomology,

`⋯ → H^l_c(U ⊓ V) → H^l_c(U) ⊕ H^l_c(V) → H^l_c(U ⊔ V) → H^{l+1}_c(U ⊓ V) → ⋯`,

for `k + l = n`. With these compatibilities, the five lemma for this ladder of exact sequences
passes Poincaré duality from `U`, `V` and `U ⊓ V` to `U ⊔ V`
(`TauCeti.bijective_poincarePairing_sup`). This is the Mayer–Vietoris step of the proof of
Poincaré duality by induction over open covers; the base case and the induction itself are not
carried out in this file.

* **Restriction and extension by zero.** For open subsets `U ≤ W`, the restriction
  `H^k(W) → H^k(U)` is adjoint to the extension by zero `H^l_c(U) → H^l_c(W)`:
  `⟨x, ext y⟩_W = ⟨x|_U, y⟩_U` (`TauCeti.poincarePairing_extendByZero`). At the level of forms,
  `φ ∧ ext ψ = ext (φ|_U ∧ ψ)` (`TauCeti.RoughForm.extendByZero_mpullback_inclusion_wedge`), and
  integration commutes with extension by zero. The maps of the two Mayer–Vietoris sequences other
  than the connecting maps are built from these, so the corresponding squares of the ladder
  commute.
* **The connecting maps.** The connecting maps `δ : H^k(U ⊓ V) → H^{k+1}(U ⊔ V)`
  (`TauCeti.deRhamCohomology.mayerVietorisδ`) and `δ_c : H^l_c(U ⊔ V) → H^{l+1}_c(U ⊓ V)`
  (`TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisδ`) are adjoint up to a sign:
  `⟨δ x, y⟩_{U ⊔ V} = (-1)^(k+1) ⟨x, δ_c y⟩_{U ⊓ V}`
  (`TauCeti.poincarePairing_mayerVietorisδ`). Write `x = [φ]` with `φ = α|_{U ⊓ V} - β|_{U ⊓ V}`, so
  that `δ x` is represented by the form equal to `dα` on `U` and `dβ` on `V`, and write `y = [τ]`
  with `τ = ext a + ext b`, so that `δ_c y` is represented by the form `θ` on `U ⊓ V` with
  `ext θ = da` and `ext θ = -db`. Integration by parts,
  `∫ dα ∧ a = -(-1)^k ∫ α ∧ da` for compactly supported `a`
  (`TauCeti.integralTopForm_cast_mextDerivₗ_wedge`), which is Stokes' theorem for `α ∧ a`, then
  turns `∫ dα ∧ a + ∫ dβ ∧ b` into `-(-1)^k ∫ (α - β) ∧ θ = (-1)^(k+1) ∫ φ ∧ θ`.

The pairing on `U ⊔ V` in degrees `(k + 1, l)` and the pairing on `U ⊓ V` in degrees `(k, l + 1)`
are taken for one orientation of `M`, indexed by `Fin (k + 1 + l)` for the first and reindexed
along `k + 1 + l = k + l + 1` for the second.

* **Duality passes to unions.** If the Poincaré pairing `H^k(W) → (H^l_c(W))^*` is bijective in
  all complementary degrees `k + l = n` for `W = U`, `V` and `U ⊓ V`, then so it is for `U ⊔ V`
  (`TauCeti.bijective_poincarePairing_sup`). In degrees `(k + 1, l)` this is the five lemma for the
  ladder from the de Rham sequence
  `H^k(U) × H^k(V) → H^k(U ⊓ V) → H^{k+1}(U ⊔ V) → H^{k+1}(U) × H^{k+1}(V) → H^{k+1}(U ⊓ V)`
  to the dual of the compactly supported sequence
  `H^l_c(U ⊓ V) → H^l_c(U) × H^l_c(V) → H^l_c(U ⊔ V) → H^{l+1}_c(U ⊓ V) → ⋯`. Its rows are exact
  because both Mayer–Vietoris sequences are and transposition of linear maps is exact
  (`Function.Exact.dualMap`), and the sign of the connecting square is absorbed into the first
  two vertical maps. In degrees `(0, l)` the ladder is cut off on the left: the de Rham
  sequence starts with an injection, and the compactly supported one ends with a surjection
  because there are no compactly supported forms of degree above the dimension `l`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5, Lemma 5.6.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Problems 18-6 to 18-8.
-/

public section

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k l : ℕ}

section Pairing

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

/-- One half of the computation of `⟨δ x, y⟩`. Let `S ≤ W` and `T ≤ S` be open subsets, `σ` a
smooth `(k + 1)`-form on `W` restricting to `dα` on `S`, `a` a compactly supported `l`-form on `S`,
and `θ` a compactly supported `(l + 1)`-form on `T` extending by zero to `da`. Then
`∫_W σ ∧ ext a = -(-1)^k ∫_T α|_T ∧ θ`, by integration by parts on `S`. -/
private theorem integralTopForm_wedge_extendByZero_eq_neg
    (o : Manifold.Orientation I M (Fin (k + 1 + l)))
    {S W T : Opens M} (hSW : S ≤ W) (hTS : T ≤ S) (σ : SmoothForm I W ℝ (k + 1))
    (α : SmoothForm I S ℝ k)
    (hσ : SmoothForm.mpullback (Opens.inclusion hSW) (contMDiff_inclusion hSW) σ = mextDerivₗ I k α)
    (a : compactlySupportedForms I S l) (θ : compactlySupportedForms I T (l + 1))
    (hθ : compactlySupportedForms.extendByZero hTS (l + 1) θ =
      compactlySupportedForms.mextDerivₗ I S l a) :
    integralTopForm (o.restrict W) (RoughForm.wedge σ.val (RoughForm.extendByZero W a.val.val)) =
      -((-1 : ℝ) ^ k * integralTopForm ((o.reindex (finCongr (add_right_comm k 1 l))).restrict T)
        (RoughForm.wedge (k := k) (l := l + 1)
          (SmoothForm.mpullback (Opens.inclusion hTS) (contMDiff_inclusion hTS) α).val
          θ.val.val)) := by
  -- Integration by parts on `S` needs `S` to be σ-compact, like every open subset of `M`.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace H S
  rw [integralTopForm_wedge_extendByZero o hSW σ a.property, hσ, ← SmoothForm.coe_wedge,
    ← integralTopForm_restrict_reindex_finCongr o (add_right_comm k 1 l) S,
    integralTopForm_cast_mextDerivₗ_wedge _ α a.property]
  have hda : mextDerivₗ I l a.val = (compactlySupportedForms.extendByZero hTS (l + 1) θ).val := by
    rw [hθ, compactlySupportedForms.coe_mextDerivₗ]
  rw [hda, SmoothForm.coe_wedge, compactlySupportedForms.coe_extendByZero]
  congr 2
  exact integralTopForm_wedge_extendByZero (k := k) (l := l + 1) _ hTS α θ.property

/-- The computation of `⟨δ x, y⟩` on representatives: with `σ` restricting to `dα` on `U` and to
`dβ` on `V`, and `θ` extending by zero to `da` on `U` and to `-db` on `V`,
`∫ σ ∧ (ext a + ext b) = -(-1)^k (∫ α ∧ θ - ∫ β ∧ θ)`, the last two integrals over `U ⊓ V`. -/
private theorem integralTopForm_wedge_add_extendByZero
    (o : Manifold.Orientation I M (Fin (k + 1 + l))) {U V : Opens M}
    (σ : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1)) (α : SmoothForm I U ℝ k)
    (β : SmoothForm I V ℝ k)
    (hσU : SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) σ =
      mextDerivₗ I k α)
    (hσV : SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) σ =
      mextDerivₗ I k β)
    (a : compactlySupportedForms I U l) (b : compactlySupportedForms I V l)
    (θ : compactlySupportedForms I (U ⊓ V : Opens M) (l + 1))
    (hθU : compactlySupportedForms.extendByZero (inf_le_left : U ⊓ V ≤ U) (l + 1) θ =
      compactlySupportedForms.mextDerivₗ I U l a)
    (hθV : compactlySupportedForms.extendByZero (inf_le_right : U ⊓ V ≤ V) (l + 1) θ =
      -compactlySupportedForms.mextDerivₗ I V l b) :
    integralTopForm (o.restrict (U ⊔ V)) (RoughForm.wedge σ.val
        (compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) l a +
          compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) l b).val.val) =
      -((-1 : ℝ) ^ k *
        (integralTopForm ((o.reindex (finCongr (add_right_comm k 1 l))).restrict (U ⊓ V))
            (RoughForm.wedge (k := k) (l := l + 1)
              (SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) α).val
              θ.val.val) -
          integralTopForm ((o.reindex (finCongr (add_right_comm k 1 l))).restrict (U ⊓ V))
            (RoughForm.wedge (k := k) (l := l + 1)
              (SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) β).val
              θ.val.val))) := by
  -- `θ` is also the form extending by zero to `d(-b)` on `V`.
  have hθV' : compactlySupportedForms.extendByZero (inf_le_right : U ⊓ V ≤ V) (l + 1) θ =
      compactlySupportedForms.mextDerivₗ I V l ((-1 : ℝ) • b) := by
    rw [hθV]
    ext1
    simp only [Submodule.coe_neg, map_smul, Submodule.coe_smul]
    exact (neg_one_smul ℝ _).symm
  have hV := integralTopForm_wedge_extendByZero_eq_neg o le_sup_right inf_le_right σ β hσV
    ((-1 : ℝ) • b) θ hθV'
  rw [Submodule.coe_smul, Submodule.coe_smul, RoughForm.extendByZero_smul,
    RoughForm.wedge_smul_right, integralTopForm_smul] at hV
  -- Split `∫ σ ∧ (ext a + ext b) = ∫ σ ∧ ext a + ∫ σ ∧ ext b` and integrate each term by parts.
  rw [← SmoothForm.coe_wedge, Submodule.coe_add, map_add,
    integralTopForm_add_of_mem_compactlySupportedForms _
    (SmoothForm.wedge_mem_compactlySupportedForms _ (Submodule.coe_mem _))
    (SmoothForm.wedge_mem_compactlySupportedForms _ (Submodule.coe_mem _)),
    SmoothForm.coe_wedge, SmoothForm.coe_wedge, compactlySupportedForms.coe_extendByZero,
    compactlySupportedForms.coe_extendByZero,
    integralTopForm_wedge_extendByZero_eq_neg o le_sup_left inf_le_left σ α hσU a θ hθU]
  linarith

/-- **The Poincaré pairing intertwines the Mayer–Vietoris connecting maps.** For open subsets `U`
and `V` of an oriented boundaryless manifold of dimension `k + 1 + l`, a de Rham class `x` on
`U ⊓ V` and a compactly supported class `y` on `U ⊔ V`,
`⟨δ x, y⟩_{U ⊔ V} = (-1)^(k+1) ⟨x, δ_c y⟩_{U ⊓ V}`, where `δ` and `δ_c` are the connecting maps of
the Mayer–Vietoris sequences of de Rham cohomology and of compactly supported cohomology, and the
orientation of `M` is reindexed along `k + 1 + l = k + l + 1` for the second pairing. -/
theorem poincarePairing_mayerVietorisδ (o : Manifold.Orientation I M (Fin (k + 1 + l)))
    {U V : Opens M} [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    (x : deRhamCohomology I (U ⊓ V : Opens M) k)
    (y : compactlySupportedDeRhamCohomology I (U ⊔ V : Opens M) l) :
    poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))
        (deRhamCohomology.mayerVietorisδ I U V k x) y =
      (-1 : ℝ) ^ (k + 1) * poincarePairing (k := k) (l := l + 1) I (U ⊓ V : Opens M)
        ((o.reindex (finCongr (add_right_comm k 1 l))).restrict (U ⊓ V)) x
        (compactlySupportedDeRhamCohomology.mayerVietorisδ I U V l y) := by
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I k x
  obtain ⟨τ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I l y
  -- Represent `δ [φ]` by the form `σ` equal to `dα` on `U` and to `dβ` on `V`, where
  -- `φ = α|_{U ⊓ V} - β|_{U ⊓ V}`.
  obtain ⟨⟨α, β⟩, hαβ⟩ := SmoothForm.surjective_mayerVietoris (I := I) (F := ℝ) (k := k) U V φ.val
  have hφ : SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) α -
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) β = φ.val := by
    simpa [sub_eq_add_neg] using hαβ
  obtain ⟨σ, hσU, hσV⟩ := exists_closedForms_mpullback_eq_mextDerivₗ α β (hφ ▸ φ.property)
  -- Represent `δ_c [τ]` by the form `θ` on `U ⊓ V` extending by zero to `da` on `U` and to `-db`
  -- on `V`, where `τ = ext a + ext b`.
  obtain ⟨⟨a, b⟩, hab⟩ := compactlySupportedForms.surjective_coprod_extendByZero (I := I) (k := l)
    U V ⟨τ.val, compactlySupportedClosedForms_le_compactlySupportedForms I l τ.property⟩
  rw [LinearMap.coprod_apply] at hab
  obtain ⟨θ, hθU, hθV⟩ := compactlySupportedForms.exists_extendByZero_eq_mextDerivₗ a b
    (by rw [hab]; exact compactlySupportedClosedForms_le_closedForms I l τ.property)
  set θ' : compactlySupportedForms I (U ⊓ V : Opens M) (l + 1) :=
    ⟨θ.val, compactlySupportedClosedForms_le_compactlySupportedForms I (l + 1) θ.property⟩
  rw [deRhamCohomology.mayerVietorisδ_mk U V φ α β hφ σ hσU hσV,
    compactlySupportedDeRhamCohomology.mayerVietorisδ_mk U V τ a b hab θ hθU hθV,
    poincarePairing_mk, poincarePairing_mk]
  rw [← congrArg (fun z : compactlySupportedForms I (U ⊔ V : Opens M) l ↦ z.val.val) hab,
    integralTopForm_wedge_add_extendByZero o σ.val α β hσU hσV a b θ' hθU hθV, ← hφ,
    integralTopForm_wedge_sub_left (k := k) (l := l + 1) _ _ _ θ'.property, pow_succ]
  ring

end Pairing

section Duality

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

/-- The Poincaré pairings of `U` and of `V` together, as a map from `H^k(U) × H^k(V)` to the dual
of `H^l_c(U) × H^l_c(V)`: `(x, y) ↦ ((a, b) ↦ ⟨x, a⟩_U + ⟨y, b⟩_V)`. -/
private def prodPoincarePairing (o : Manifold.Orientation I M (Fin (k + l))) (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V] :
    deRhamCohomology I U k × deRhamCohomology I V k →ₗ[ℝ]
      Module.Dual ℝ (compactlySupportedDeRhamCohomology I U l ×
        compactlySupportedDeRhamCohomology I V l) :=
  (Module.dualProdDualEquivDual ℝ _ _).toLinearMap ∘ₗ
    (poincarePairing I U (o.restrict U)).prodMap (poincarePairing I V (o.restrict V))

omit [SigmaCompactSpace M] in
private theorem prodPoincarePairing_apply (o : Manifold.Orientation I M (Fin (k + l)))
    {U V : Opens M} [SigmaCompactSpace U] [SigmaCompactSpace V]
    (x : deRhamCohomology I U k × deRhamCohomology I V k)
    (y : compactlySupportedDeRhamCohomology I U l × compactlySupportedDeRhamCohomology I V l) :
    prodPoincarePairing o U V x y =
      poincarePairing I U (o.restrict U) x.1 y.1 + poincarePairing I V (o.restrict V) x.2 y.2 := by
  simp [prodPoincarePairing]

omit [SigmaCompactSpace M] in
private theorem bijective_prodPoincarePairing (o : Manifold.Orientation I M (Fin (k + l)))
    {U V : Opens M} [SigmaCompactSpace U] [SigmaCompactSpace V]
    (hU : Function.Bijective (poincarePairing I U (o.restrict U)))
    (hV : Function.Bijective (poincarePairing I V (o.restrict V))) :
    Function.Bijective (prodPoincarePairing o U V) :=
  (Module.dualProdDualEquivDual ℝ _ _).bijective.comp (hU.prodMap hV)

omit [SigmaCompactSpace M] in
/-- The square of the Poincaré ladder at `H^k(U ⊔ V)`: the pairing intertwines the restrictions
`H^k(U ⊔ V) → H^k(U) × H^k(V)` with the dual of the sum of the extensions by zero
`H^l_c(U) × H^l_c(V) → H^l_c(U ⊔ V)`. -/
private theorem dualMap_mayerVietorisFromProd_comp_poincarePairing
    (o : Manifold.Orientation I M (Fin (k + l))) {U V : Opens M} [SigmaCompactSpace U]
    [SigmaCompactSpace V] [SigmaCompactSpace (U ⊔ V : Opens M)] :
    (compactlySupportedDeRhamCohomology.mayerVietorisFromProd I U V l).dualMap ∘ₗ
        poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V)) =
      prodPoincarePairing o U V ∘ₗ deRhamCohomology.mayerVietorisToProd I U V k := by
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  simp [prodPoincarePairing_apply, poincarePairing_extendByZero]

omit [SigmaCompactSpace M] in
/-- The square of the Poincaré ladder at `H^k(U) × H^k(V)`: the pairings intertwine the difference
of the restrictions `H^k(U) × H^k(V) → H^k(U ⊓ V)` with the dual of `(ext, -ext)`,
`H^l_c(U ⊓ V) → H^l_c(U) × H^l_c(V)`. -/
private theorem dualMap_mayerVietorisToProd_comp_prodPoincarePairing
    (o : Manifold.Orientation I M (Fin (k + l))) {U V : Opens M} [SigmaCompactSpace U]
    [SigmaCompactSpace V] [SigmaCompactSpace (U ⊓ V : Opens M)] :
    (compactlySupportedDeRhamCohomology.mayerVietorisToProd I U V l).dualMap ∘ₗ
        prodPoincarePairing o U V =
      poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)) ∘ₗ
        deRhamCohomology.mayerVietorisFromProd I U V k := by
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  simp [prodPoincarePairing_apply, poincarePairing_extendByZero, sub_eq_add_neg]

/-- Poincaré duality in degrees `(0, l)` passes from `U`, `V` and `U ⊓ V` to `U ⊔ V`; in degree
`0` the de Rham Mayer–Vietoris sequence starts with an injection, and in the top degree `l` the
compactly supported one ends with a surjection. -/
private theorem bijective_poincarePairing_sup_zero (o : Manifold.Orientation I M (Fin (0 + l)))
    {U V : Opens M} [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    (hU : Function.Bijective (poincarePairing I U (o.restrict U)))
    (hV : Function.Bijective (poincarePairing I V (o.restrict V)))
    (hUV : Function.Injective (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)))) :
    Function.Bijective (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))) :=
  LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (f₁ := deRhamCohomology.mayerVietorisToProd I U V 0)
    (f₂ := deRhamCohomology.mayerVietorisFromProd I U V 0)
    (g₁ := (compactlySupportedDeRhamCohomology.mayerVietorisFromProd I U V l).dualMap)
    (g₂ := (compactlySupportedDeRhamCohomology.mayerVietorisToProd I U V l).dualMap)
    (i₂ := prodPoincarePairing o U V)
    (hc₁ := dualMap_mayerVietorisFromProd_comp_poincarePairing o)
    (hc₂ := dualMap_mayerVietorisToProd_comp_prodPoincarePairing o)
    (hf₁ := deRhamCohomology.exact_mayerVietorisToProd_fromProd U V 0)
    (hg₁ := (compactlySupportedDeRhamCohomology.exact_mayerVietorisToProd_fromProd U V l).dualMap)
    (hi₂ := bijective_prodPoincarePairing o hU hV) (hi₃ := hUV)
    (hf₀ := deRhamCohomology.mayerVietorisToProd_zero_injective U V)
    (hg₀ := LinearMap.dualMap_injective_of_surjective
      (compactlySupportedDeRhamCohomology.mayerVietorisFromProd_surjective U V
        (o.card_eq.symm.trans (by simp)).le))

/-- Poincaré duality in degrees `(k + 1, l)` passes to `U ⊔ V` from duality on `U`, `V` and
`U ⊓ V` in degrees `(k, l + 1)` and `(k + 1, l)`, by the five lemma for the ladder formed by the
Mayer–Vietoris sequence of de Rham cohomology and the dual of the compactly supported one. The
connecting square commutes up to the sign `(-1)^(k+1)`, which is absorbed into the first two
vertical maps. -/
private theorem bijective_poincarePairing_sup_succ
    (o : Manifold.Orientation I M (Fin (k + 1 + l))) {U V : Opens M} [SigmaCompactSpace U]
    [SigmaCompactSpace V] [SigmaCompactSpace (U ⊓ V : Opens M)]
    [SigmaCompactSpace (U ⊔ V : Opens M)]
    (hU : Function.Bijective (poincarePairing (k := k) (l := l + 1) I U
      ((o.reindex (finCongr (add_right_comm k 1 l))).restrict U)))
    (hV : Function.Bijective (poincarePairing (k := k) (l := l + 1) I V
      ((o.reindex (finCongr (add_right_comm k 1 l))).restrict V)))
    (hUV : Function.Bijective (poincarePairing (k := k) (l := l + 1) I (U ⊓ V : Opens M)
      ((o.reindex (finCongr (add_right_comm k 1 l))).restrict (U ⊓ V))))
    (hU' : Function.Bijective (poincarePairing I U (o.restrict U)))
    (hV' : Function.Bijective (poincarePairing I V (o.restrict V)))
    (hUV' : Function.Injective (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)))) :
    Function.Bijective (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))) := by
  set o' := o.reindex (finCongr (add_right_comm k 1 l))
  refine LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (f₁ := deRhamCohomology.mayerVietorisFromProd I U V k)
    (f₂ := deRhamCohomology.mayerVietorisδ I U V k)
    (f₃ := deRhamCohomology.mayerVietorisToProd I U V (k + 1))
    (f₄ := deRhamCohomology.mayerVietorisFromProd I U V (k + 1))
    (g₁ := (compactlySupportedDeRhamCohomology.mayerVietorisToProd I U V (l + 1)).dualMap)
    (g₂ := (compactlySupportedDeRhamCohomology.mayerVietorisδ I U V l).dualMap)
    (g₃ := (compactlySupportedDeRhamCohomology.mayerVietorisFromProd I U V l).dualMap)
    (g₄ := (compactlySupportedDeRhamCohomology.mayerVietorisToProd I U V l).dualMap)
    (i₁ := ((-1 : ℝ) ^ (k + 1)) • prodPoincarePairing (k := k) (l := l + 1) o' U V)
    (i₂ := ((-1 : ℝ) ^ (k + 1)) •
      poincarePairing (k := k) (l := l + 1) I (U ⊓ V : Opens M) (o'.restrict (U ⊓ V)))
    (i₄ := prodPoincarePairing o U V)
    (hc₃ := dualMap_mayerVietorisFromProd_comp_poincarePairing o)
    (hc₄ := dualMap_mayerVietorisToProd_comp_prodPoincarePairing o)
    (hf₁ := deRhamCohomology.exact_mayerVietorisFromProd_δ U V k)
    (hf₂ := deRhamCohomology.exact_mayerVietorisδ_toProd U V k)
    (hf₃ := deRhamCohomology.exact_mayerVietorisToProd_fromProd U V (k + 1))
    (hg₁ := (compactlySupportedDeRhamCohomology.exact_mayerVietorisδ_toProd U V l).dualMap)
    (hg₂ := (compactlySupportedDeRhamCohomology.exact_mayerVietorisFromProd_δ U V l).dualMap)
    (hg₃ := (compactlySupportedDeRhamCohomology.exact_mayerVietorisToProd_fromProd U V l).dualMap)
    (hi₄ := bijective_prodPoincarePairing o hU' hV') (hi₅ := hUV') (hc₁ := ?_) (hc₂ := ?_)
    (hi₁ := ?_) (hi₂ := ?_)
  · rw [LinearMap.comp_smul, LinearMap.smul_comp,
      dualMap_mayerVietorisToProd_comp_prodPoincarePairing (k := k) (l := l + 1) o']
  · refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
    simp [poincarePairing_mayerVietorisδ o x y, o']
  -- Multiplication by the sign `(-1)^(k+1)` is bijective.
  · rw [LinearMap.coe_smul]
    exact (((isUnit_neg_one (α := ℝ)).pow (k + 1)).smul_bijective.comp
      (bijective_prodPoincarePairing (k := k) (l := l + 1) o' hU hV)).2
  · rw [LinearMap.coe_smul]
    exact ((isUnit_neg_one (α := ℝ)).pow (k + 1)).smul_bijective.comp hUV

/-- **The Mayer–Vietoris step of Poincaré duality.** Let `M` be an oriented boundaryless manifold
of dimension `n`, and `U` and `V` open subsets of `M`, with the orientations restricted from `M`.
If the Poincaré pairing `H^k_dR(W) → (H^l_c(W))^*` is bijective in all complementary degrees
`k + l = n` for `W = U`, `V` and `U ⊓ V`, then it is bijective in all complementary degrees for
`W = U ⊔ V`. -/
theorem bijective_poincarePairing_sup {n : ℕ} (o : Manifold.Orientation I M (Fin n))
    {U V : Opens M} [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    (hU : ∀ k l (h : k + l = n), Function.Bijective
      (poincarePairing (k := k) (l := l) I U ((o.reindex (finCongr h.symm)).restrict U)))
    (hV : ∀ k l (h : k + l = n), Function.Bijective
      (poincarePairing (k := k) (l := l) I V ((o.reindex (finCongr h.symm)).restrict V)))
    (hUV : ∀ k l (h : k + l = n), Function.Bijective
      (poincarePairing (k := k) (l := l) I (U ⊓ V : Opens M)
        ((o.reindex (finCongr h.symm)).restrict (U ⊓ V))))
    (k l : ℕ) (h : k + l = n) :
    Function.Bijective (poincarePairing (k := k) (l := l) I (U ⊔ V : Opens M)
      ((o.reindex (finCongr h.symm)).restrict (U ⊔ V))) := by
  subst h
  cases k with
  | zero =>
    exact bijective_poincarePairing_sup_zero _ (hU 0 l rfl) (hV 0 l rfl) (hUV 0 l rfl).1
  | succ k =>
    have hU' := hU (k + 1) l rfl
    have hV' := hV (k + 1) l rfl
    have hUV' := hUV (k + 1) l rfl
    simp only [finCongr_refl, Manifold.Orientation.reindex_refl] at hU' hV' hUV' ⊢
    exact bijective_poincarePairing_sup_succ o (hU k (l + 1) (by lia)) (hV k (l + 1) (by lia))
      (hUV k (l + 1) (by lia)) hU' hV' hUV'.1

end Duality

end TauCeti
