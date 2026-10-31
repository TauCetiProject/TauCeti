/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.UCB.CompRight

/-!
# Bounded uniformly continuous functions on a product of groups

For topological groups `G` and `H` and a function `f` in `TauCeti.UCB (G × H)`, every slice
`y ↦ f (x, y)` lies in `UCB H`, and the slices depend uniformly continuously on `x`: the slice at
`u * x` is uniformly close to the slice at `x` for all `u` near `1`, because `(u, 1)` is near `1`
in `G × H`. Consequently, applying a continuous linear functional `Λ` on `UCB H` to the slices,

```text
(UCB.applyRight Λ f) x = Λ (y ↦ f (x, y)),
```

gives a function in `UCB G`. When `Λ` is a mean this averages `f` over the second variable; a
second mean on `UCB G` then gives the iterated mean on `UCB (G × H)` that shows that products of
amenable groups are amenable.

## Main definitions

* `TauCeti.UCB.compProdMk x`: the slice `f ↦ f (x, ·)`, a unital algebra homomorphism
  `UCB (G × H) →ₐ[ℝ] UCB H`.
* `TauCeti.UCB.applyRight Λ`: the continuous linear map `UCB (G × H) →L[ℝ] UCB G` applying a
  continuous linear functional `Λ` on `UCB H` to the slices.

## Main results

* `TauCeti.UCB.forall_eventually_dist_compProdMk_mul_lt`: the slice of `f` at `u * x` is uniformly
  close to the slice at `x` for all `u` near `1`.
* `TauCeti.UCB.compProdMk_leftTranslation`: the slice of `L_(g, h) f` at `x` is `L_h` applied to the
  slice of `f` at `g⁻¹ * x`.
* `TauCeti.UCB.applyRight_compRightAlgHom_fst`, `TauCeti.UCB.applyRight_compRightAlgHom_snd`:
  `applyRight Λ` multiplies a function of `x` alone by `Λ 1`, and sends a function `f` of `y` alone
  to the constant `Λ f`.
* `TauCeti.UCB.applyRight_leftTranslation`: if `Λ` is invariant under left translation, then
  `applyRight Λ` intertwines `L_(g, h)` with `L_g`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1 and
  Proposition G.2.2.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The slice `y ↦ f (x, y)` of a function in `ucb (G × H)` lies in `ucb H`. -/
theorem compContinuous_prodMk_mem_ucb {f : G × H →ᵇ ℝ} (hf : f ∈ ucb (G × H)) (x : G) :
    f.compContinuous ((ContinuousMap.const H x).prodMk (ContinuousMap.id H)) ∈ ucb H := by
  have h : Tendsto (fun u : H => ((1 : G), u)) (𝓝 1) (𝓝 1) :=
    (continuous_const.prodMk continuous_id).tendsto' 1 1 rfl
  rw [mem_ucb_iff] at hf ⊢
  intro ε hε
  filter_upwards [h.eventually (hf ε hε)] with u hu y
  simpa using hu (x, y)

namespace UCB

/-- The slice `f ↦ f (x, ·)` at `x : G`, as a unital algebra homomorphism from `UCB (G × H)` to
`UCB H`. -/
def compProdMk (x : G) : UCB (G × H) →ₐ[ℝ] UCB H where
  toFun f := ⟨(f : G × H →ᵇ ℝ).compContinuous ((ContinuousMap.const H x).prodMk
    (ContinuousMap.id H)), compContinuous_prodMk_mem_ucb f.2 x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem compProdMk_apply (x : G) (f : UCB (G × H)) (y : H) :
    (compProdMk x f : H →ᵇ ℝ) y = (f : G × H →ᵇ ℝ) (x, y) :=
  (rfl)

/-- The slice of a function of the first variable alone is constant. -/
@[simp]
theorem compProdMk_compRightAlgHom_fst (x : G) (f : UCB G) :
    compProdMk x (compRightAlgHom (ContinuousMonoidHom.fst G H) f) =
      algebraMap ℝ (UCB H) ((f : G →ᵇ ℝ) x) := by
  ext
  simp

/-- The slice of a function of the second variable alone is that function. -/
@[simp]
theorem compProdMk_compRightAlgHom_snd (x : G) (f : UCB H) :
    compProdMk x (compRightAlgHom (ContinuousMonoidHom.snd G H) f) = f := by
  ext
  simp

/-- The slice of `L_(g, h) f` at `x` is the left translate by `h` of the slice of `f` at
`g⁻¹ * x`. -/
theorem compProdMk_leftTranslation (x : G) (p : G × H) (f : UCB (G × H)) :
    compProdMk x (leftTranslation p f) = leftTranslation p.2 (compProdMk (p.1⁻¹ * x) f) := by
  ext
  simp [Prod.mul_def]

/-- Slicing preserves the pointwise order. -/
theorem monotone_compProdMk (x : G) : Monotone (compProdMk (H := H) x) :=
  fun _ _ h => le_def.2 fun y => le_def.1 h (x, y)

/-- The slices of `f` depend uniformly continuously on the first variable: the slice at `u * x` is
uniformly close to the slice at `x` for all `u` near `1`. -/
theorem forall_eventually_dist_compProdMk_mul_lt (f : UCB (G × H)) :
    ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, dist (compProdMk (u * x) f) (compProdMk x f) < ε := by
  have h : Tendsto (fun u : G => (u, (1 : H))) (𝓝 1) (𝓝 1) :=
    (continuous_id.prodMk continuous_const).tendsto' 1 1 rfl
  intro ε hε
  filter_upwards [h.eventually ((mem_ucb_iff.1 f.2) (ε / 2) (half_pos hε))] with u hu x
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun y => ?_)
    (half_lt_self hε)
  simpa [Real.dist_eq] using (hu (x, y)).le

/-- Slicing does not increase the supremum norm. -/
theorem norm_compProdMk_apply_le (x : G) (f : UCB (G × H)) : ‖compProdMk x f‖ ≤ ‖f‖ :=
  (f : G × H →ᵇ ℝ).norm_compContinuous_le _

variable (Λ : UCB H →L[ℝ] ℝ)

/-- `x ↦ Λ (f (x, ·))` is uniformly continuous for the right uniformity of `G`. -/
private theorem uniformContinuous_apply_compProdMk (f : UCB (G × H)) :
    (letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
     UniformContinuous fun x => Λ (compProdMk x f)) :=
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  Λ.uniformContinuous.comp
    ((uniformContinuous_rightUniformSpace_iff _).2 (forall_eventually_dist_compProdMk_mul_lt f))

private theorem norm_apply_compProdMk_le (f : UCB (G × H)) (x : G) :
    ‖Λ (compProdMk x f)‖ ≤ ‖Λ‖ * ‖f‖ :=
  (Λ.le_opNorm _).trans (by gcongr; exact norm_compProdMk_apply_le x f)

/-- The bounded continuous function `x ↦ Λ (f (x, ·))`. -/
private def applyRightAux (f : UCB (G × H)) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => Λ (compProdMk x f))
    (letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
     (uniformContinuous_apply_compProdMk Λ f).continuous)
    (‖Λ‖ * ‖f‖) (norm_apply_compProdMk_le Λ f)

/-- Applying a continuous linear functional `Λ` on `UCB H` to the slices of a function on `G × H`:
`(applyRight Λ f) x = Λ (f (x, ·))`, as a continuous linear map from `UCB (G × H)` to `UCB G`. -/
def applyRight : UCB (G × H) →L[ℝ] UCB G :=
  LinearMap.mkContinuous
    { toFun f := ⟨applyRightAux Λ f,
        mem_ucb_iff_uniformContinuous.2 (uniformContinuous_apply_compProdMk Λ f)⟩
      map_add' f f' := by
        ext x
        simp [applyRightAux]
      map_smul' c f := by
        ext x
        simp [applyRightAux] }
    ‖Λ‖ fun f => BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
      (by positivity) (norm_apply_compProdMk_le Λ f)

@[simp]
theorem applyRight_apply (f : UCB (G × H)) (x : G) :
    (applyRight Λ f : G →ᵇ ℝ) x = Λ (compProdMk x f) :=
  (rfl)

/-- `applyRight Λ` sends a function of the first variable alone to its multiple by `Λ 1`. -/
@[simp]
theorem applyRight_compRightAlgHom_fst (f : UCB G) :
    applyRight Λ (compRightAlgHom (ContinuousMonoidHom.fst G H) f) = Λ 1 • f := by
  ext x
  simp [Algebra.algebraMap_eq_smul_one, mul_comm]

/-- `applyRight Λ` sends a function of the second variable alone to the constant `Λ f`. -/
@[simp]
theorem applyRight_compRightAlgHom_snd (f : UCB H) :
    applyRight Λ (compRightAlgHom (ContinuousMonoidHom.snd G H) f) =
      algebraMap ℝ (UCB G) (Λ f) := by
  ext x
  simp

/-- `applyRight Λ` sends the constant function `1` to the constant `Λ 1`. -/
@[simp]
theorem applyRight_one : applyRight Λ (1 : UCB (G × H)) = algebraMap ℝ (UCB G) (Λ 1) := by
  ext x
  simp

/-- `applyRight Λ` has operator norm at most `‖Λ‖`. -/
theorem norm_applyRight_le : ‖applyRight (G := G) Λ‖ ≤ ‖Λ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg Λ) _

/-- If `Λ` is invariant under left translation, then `applyRight Λ` intertwines left translation
by `(g, h)` on `UCB (G × H)` with left translation by `g` on `UCB G`. -/
theorem applyRight_leftTranslation (hΛ : ∀ (h : H) (f : UCB H), Λ (leftTranslation h f) = Λ f)
    (p : G × H) (f : UCB (G × H)) :
    applyRight Λ (leftTranslation p f) = leftTranslation p.1 (applyRight Λ f) := by
  ext x
  simp [compProdMk_leftTranslation, hΛ]

end UCB

end TauCeti
