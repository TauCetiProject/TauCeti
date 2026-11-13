/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coprod.Finiteness
public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Discrimination
public import TauCeti.GroupTheory.LimitGroup.MarkedGroup
import TauCeti.GroupTheory.Coprod.Conj
import TauCeti.GroupTheory.LimitGroup.Characterization

/-!
# The free product `ℤ² ∗ ℤ`

The free product `ℤ² ∗ ℤ = ⟨a, b, t | [a, b] = 1⟩` of the free abelian group `ℤ²` on `a = (1, 0)`
and `b = (0, 1)` with the infinite cyclic group on `t` is the extension
`F(a, t) ∗_{⟨a⟩} (⟨a⟩ × ⟨b⟩)` of the centralizer `⟨a⟩` of the basis element `a` of the free group
`F(a, t)`. By Baumslag's theorem it is therefore fully residually free, and, being finitely
generated, a limit group. Unlike in a free group, not every centralizer of a nontrivial element
is cyclic: the centralizer of every nontrivial element of the factor `ℤ²`, for instance of
`(1, 0)`, is that factor `ℤ²`. Equivalently, the equation `[x, (1, 0)] = 1` over `ℤ² ∗ ℤ` has
exactly the solutions `x ∈ ℤ²`. Distinct elements of `ℤ²`, such as `(1, 0)` and `(0, 1)`, are not
conjugate in `ℤ² ∗ ℤ`.

## Main definitions

* `TauCeti.LimitGroup.IntSqCoprodInt`: the free product `ℤ² ∗ ℤ`.
* `TauCeti.LimitGroup.IntSqCoprodInt.equivCentralizerExt`: `ℤ² ∗ ℤ` is isomorphic to the
  extension of the centralizer of the basis element `a` of `F(a, t)` by `ℤ`.

## Main results

* `TauCeti.LimitGroup.IntSqCoprodInt.isFullyResiduallyFree`: `ℤ² ∗ ℤ` is fully residually free.
* `TauCeti.LimitGroup.IntSqCoprodInt.isLimitGroup`: `ℤ² ∗ ℤ` is a limit group.
* `TauCeti.LimitGroup.IntSqCoprodInt.centralizer_inl_eq_range_inl`: the centralizer of a
  nontrivial element of the factor `ℤ²` is that factor.
* `TauCeti.LimitGroup.IntSqCoprodInt.not_isCyclic_centralizer_inl`: the centralizer of an element
  of the factor `ℤ²` is not cyclic.
* `TauCeti.LimitGroup.IntSqCoprodInt.not_isConj_inl_of_ne`: distinct elements of the factor `ℤ²`,
  such as `(1, 0)` and `(0, 1)`, are not conjugate.
* `TauCeti.LimitGroup.IntSqCoprodInt.V_singleton_commutatorElement_inl`: over `ℤ² ∗ ℤ`, the
  solutions of the equation `[x, v] = 1` for a nontrivial `v ∈ ℤ²` are exactly the points whose
  `x`-coordinate lies in `ℤ²`.

## Implementation notes

The centralizer is computed with the retractions `r_k` of the extension of centralizers onto
`F(a, t)` sending `b` to `a ^ k`, which keep any given nontrivial element nontrivial for all large
`k`. Let `g` commute with a nontrivial `v = (v₁, v₂) ∈ ℤ²`, and let `n = (fst g)⁻¹ g`, where `fst`
kills `t`. For large `k` with `v₁ + k v₂ ≠ 0`, the element `r_k n` commutes with the nontrivial
power `r_k v = a ^ (v₁ + k v₂)`, hence with `a`, so it is a power of `a`; its exponent is that of
`r_k (fst n) = 1`, so `r_k n = 1`. Hence `n = 1` and `g = fst g ∈ ℤ²`.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), Proposition 3.1, and §3.2, Definition 3.2 and Proposition 3.4 (extensions of
  centralizers of free groups).
* B. Baumslag, *Residually free groups*, Proc. London Math. Soc. (3) 17 (1967), 402–418.
-/

public section

open Monoid.Coprod Subgroup
open scoped commutatorElement

namespace TauCeti.LimitGroup

/-- The free product `ℤ² ∗ ℤ` of the free abelian group of rank two with the infinite cyclic
group. -/
abbrev IntSqCoprodInt : Type :=
  Multiplicative (ℤ × ℤ) ∗ Multiplicative ℤ

namespace IntSqCoprodInt

/-- The basis element `a` of `F(a, t)` commutes with the new letter of `F(a, t)(a, ℤ)`. -/
private theorem commute_of_t :
    Commute (CentralizerExt.of (FreeGroup.of 0) : CentralizerExt (FreeGroup.of (0 : Fin 2)) 1)
      (CentralizerExt.t 0) :=
  CentralizerExt.commute_of_t (mem_centralizer_singleton_iff.2 rfl) 0

/-- The map `ℤ² ∗ ℤ →* F(a, t)(a, ℤ)`, `(m, n) ↦ a ^ m * s ^ n`, `t ↦ t`, where `s` is the new
letter. -/
private noncomputable def toCentralizerExt :
    IntSqCoprodInt →* CentralizerExt (FreeGroup.of (0 : Fin 2)) 1 :=
  lift (((zpowersHom _ (CentralizerExt.of (FreeGroup.of 0))).noncommCoprod
      (zpowersHom _ (CentralizerExt.t 0)) fun m n => by
        simpa only [zpowersHom_apply] using commute_of_t.zpow_zpow m.toAdd n.toAdd).comp
      (MulEquiv.prodMultiplicative ℤ ℤ).toMonoidHom)
    (zpowersHom _ (CentralizerExt.of (FreeGroup.of 1)))

private theorem toCentralizerExt_inl (v : Multiplicative (ℤ × ℤ)) : toCentralizerExt (inl v) =
    CentralizerExt.of (FreeGroup.of 0) ^ v.toAdd.1 * CentralizerExt.t 0 ^ v.toAdd.2 := by
  simp [toCentralizerExt]

private theorem toCentralizerExt_inr (n : Multiplicative ℤ) :
    toCentralizerExt (inr n) = CentralizerExt.of (FreeGroup.of 1) ^ n.toAdd := by
  simp [toCentralizerExt]

/-- The map `F(a, t)(a, ℤ) →* ℤ² ∗ ℤ`, `a ↦ (1, 0)`, `t ↦ t`, `s ↦ (0, 1)`. It is well defined
because the centralizer of `a` in `F(a, t)` is generated by `a`. -/
private def ofCentralizerExt : CentralizerExt (FreeGroup.of (0 : Fin 2)) 1 →* IntSqCoprodInt :=
  CentralizerExt.lift (FreeGroup.lift ![inl (.ofAdd (1, 0)), inr (.ofAdd 1)])
    (fun _ => inl (.ofAdd (0, 1))) (fun _ _ => Commute.refl _) fun c hc _ => by
      obtain ⟨k, rfl⟩ := FreeGroup.mem_zpowers_of_of_commute (mem_centralizer_singleton_iff.1 hc)
      simpa using ((Commute.all _ _).map inl).zpow_left k

private theorem ofCentralizerExt_of (w : FreeGroup (Fin 2)) :
    ofCentralizerExt (CentralizerExt.of w) =
      FreeGroup.lift ![inl (.ofAdd (1, 0)), inr (.ofAdd 1)] w :=
  CentralizerExt.lift_of _ _ _ _ w

private theorem ofCentralizerExt_t (i : Fin 1) :
    ofCentralizerExt (CentralizerExt.t i) = inl (.ofAdd (0, 1)) :=
  CentralizerExt.lift_t _ _ _ _ i

/-- Every `v ∈ ℤ²` is `(1, 0) ^ v₁ * (0, 1) ^ v₂`. -/
private theorem ofAdd_zpow_mul_ofAdd_zpow (v : Multiplicative (ℤ × ℤ)) :
    (.ofAdd (1, 0) : Multiplicative (ℤ × ℤ)) ^ v.toAdd.1 * .ofAdd (0, 1) ^ v.toAdd.2 = v := by
  refine Multiplicative.toAdd.injective (Prod.ext ?_ ?_) <;> simp

private theorem ofCentralizerExt_comp_toCentralizerExt :
    ofCentralizerExt.comp toCentralizerExt = .id _ := by
  refine hom_ext (MonoidHom.ext fun v => ?_) (MonoidHom.ext_mint ?_)
  · simp only [MonoidHom.coe_comp, Function.comp_apply, toCentralizerExt_inl, map_mul, map_zpow,
      ofCentralizerExt_of, ofCentralizerExt_t, FreeGroup.lift_apply_of, Matrix.cons_val_zero]
    simp [← map_zpow, ← map_mul, ofAdd_zpow_mul_ofAdd_zpow]
  · simp [toCentralizerExt_inr, ofCentralizerExt_of]

private theorem toCentralizerExt_comp_ofCentralizerExt :
    toCentralizerExt.comp ofCentralizerExt = .id _ := by
  refine CentralizerExt.hom_ext (FreeGroup.ext_hom _ _ fun i => ?_) fun i => ?_
  · fin_cases i <;> simp [ofCentralizerExt_of, toCentralizerExt_inl, toCentralizerExt_inr]
  · simp [ofCentralizerExt_t, toCentralizerExt_inl, Subsingleton.elim i 0]

/-- `ℤ² ∗ ℤ` is the extension `F(a, t) ∗_{⟨a⟩} (⟨a⟩ × ⟨s⟩)` of the centralizer of the basis
element `a` of the free group `F(a, t)` by `ℤ = ⟨s⟩`: the isomorphism sends `(1, 0)` to `a`,
`(0, 1)` to the new letter `s = CentralizerExt.t 0`, and the generator `t` of the factor `ℤ` to
the basis element `t` of `F(a, t)`. -/
noncomputable def equivCentralizerExt :
    IntSqCoprodInt ≃* CentralizerExt (FreeGroup.of (0 : Fin 2)) 1 :=
  toCentralizerExt.toMulEquiv ofCentralizerExt ofCentralizerExt_comp_toCentralizerExt
    toCentralizerExt_comp_ofCentralizerExt

@[simp]
theorem equivCentralizerExt_inl (v : Multiplicative (ℤ × ℤ)) : equivCentralizerExt (inl v) =
    CentralizerExt.of (FreeGroup.of 0) ^ v.toAdd.1 * CentralizerExt.t 0 ^ v.toAdd.2 :=
  toCentralizerExt_inl v

@[simp]
theorem equivCentralizerExt_inr (n : Multiplicative ℤ) :
    equivCentralizerExt (inr n) = CentralizerExt.of (FreeGroup.of 1) ^ n.toAdd :=
  toCentralizerExt_inr n

@[simp]
theorem equivCentralizerExt_symm_of (w : FreeGroup (Fin 2)) :
    equivCentralizerExt.symm (CentralizerExt.of w) =
      FreeGroup.lift ![inl (.ofAdd (1, 0)), inr (.ofAdd 1)] w :=
  ofCentralizerExt_of w

@[simp]
theorem equivCentralizerExt_symm_t (i : Fin 1) :
    equivCentralizerExt.symm (CentralizerExt.t i) = inl (.ofAdd (0, 1)) :=
  ofCentralizerExt_t i

/-- `ℤ² ∗ ℤ` is fully residually free. -/
theorem isFullyResiduallyFree : IsFullyResiduallyFree IntSqCoprodInt :=
  (isFullyResiduallyFree_centralizerExt isFullyResiduallyFree_of_isFreeGroup
    (FreeGroup.of_ne_one 0)).of_injective (f := equivCentralizerExt.toMonoidHom)
    equivCentralizerExt.injective

/-- `ℤ² ∗ ℤ` is a limit group: it is finitely generated and fully residually free. -/
theorem isLimitGroup : IsLimitGroup IntSqCoprodInt :=
  isFullyResiduallyFree.isLimitGroup

/-- The exponent sum of `a` in `F(a, t)`. -/
private def expA : FreeGroup (Fin 2) →* Multiplicative ℤ :=
  FreeGroup.lift ![.ofAdd 1, 1]

private theorem expA_of_zero_zpow (m : ℤ) : expA (FreeGroup.of 0 ^ m) = .ofAdd m := by
  simp [expA, ← ofAdd_zsmul]

/-- After a retraction onto `F(a, t)`, the exponent sum of `a` only depends on the image in `ℤ²`,
since `t` has exponent sum zero. -/
private theorem expA_retraction_equivCentralizerExt (k : ℤ) (g : IntSqCoprodInt) :
    expA (CentralizerExt.retraction (fun _ => k) (equivCentralizerExt g)) =
      expA (CentralizerExt.retraction (fun _ => k) (equivCentralizerExt (inl (fst g)))) := by
  let f := expA.comp ((CentralizerExt.retraction fun _ => k).comp equivCentralizerExt.toMonoidHom)
  have hf : f = (f.comp inl).comp fst :=
    hom_ext (MonoidHom.ext fun v => by simp) (MonoidHom.ext_mint (by simp [f, expA]))
  exact DFunLike.congr_fun hf g

private theorem retraction_equivCentralizerExt_inl (k : ℤ) (v : Multiplicative (ℤ × ℤ)) :
    CentralizerExt.retraction (fun _ => k) (equivCentralizerExt (inl v)) =
      FreeGroup.of 0 ^ (v.toAdd.1 + k * v.toAdd.2) := by
  simp [zpow_add, zpow_mul]

/-- For `v ≠ 1` and every `N`, some `k ≥ N` makes `v₁ + k v₂` nonzero. -/
private theorem exists_le_add_mul_ne_zero {v : Multiplicative (ℤ × ℤ)} (hv : v ≠ 1) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ v.toAdd.1 + k * v.toAdd.2 ≠ 0 := by
  by_contra! h
  have h₀ := h N le_rfl
  have h₁ := h (N + 1) (Nat.le_succ N)
  refine hv (Multiplicative.toAdd.injective (Prod.ext ?_ ?_)) <;> push_cast at h₁ <;>
    simp <;> nlinarith

/-- An element of `ℤ² ∗ ℤ` commuting with a nontrivial `v ∈ ℤ²` and killed by the projection onto
`ℤ²` is trivial. -/
private theorem eq_one_of_commute_of_fst_eq_one {v : Multiplicative (ℤ × ℤ)} (hv : v ≠ 1)
    {n : IntSqCoprodInt} (hn : Commute n (inl v)) (hfst : fst n = 1) : n = 1 := by
  by_contra hne
  have hF := isFullyResiduallyFree_of_isFreeGroup (G := FreeGroup (Fin 2))
  obtain ⟨N, hN⟩ := CentralizerExt.exists_forall_retraction_ne_one hF.isBP hF.isCSA
    (FreeGroup.of_ne_one 0)
    ((map_ne_one_iff equivCentralizerExt equivCentralizerExt.injective).2 hne)
  obtain ⟨k, hk, hvk⟩ := exists_le_add_mul_ne_zero hv N
  let ρ := (CentralizerExt.retraction fun _ => (k : ℤ)).comp equivCentralizerExt.toMonoidHom
  have hρv : ρ (inl v) = FreeGroup.of 0 ^ (v.toAdd.1 + k * v.toAdd.2) :=
    retraction_equivCentralizerExt_inl _ v
  -- `ρ n` commutes with a nontrivial power of `a`, hence with `a`, so it is a power of `a`.
  have hpow : FreeGroup.of (0 : Fin 2) ^ (v.toAdd.1 + k * v.toAdd.2) ≠ 1 := fun h =>
    hvk (by simpa only [expA_of_zero_zpow, map_one, ofAdd_eq_one] using congrArg expA h)
  have ha : Commute (ρ n) (FreeGroup.of 0) :=
    IsFreeGroup.commute_of_commute hpow (hρv ▸ hn.map ρ) ((Commute.refl _).zpow_left _)
  obtain ⟨j, hj⟩ := FreeGroup.mem_zpowers_of_of_commute ha
  -- Its exponent sum of `a` is that of `ρ (inl (fst n)) = 1`, so it is trivial.
  have hexp : expA (ρ n) = 1 := by
    simpa [ρ, hfst] using expA_retraction_equivCentralizerExt k n
  rw [← hj, expA_of_zero_zpow, ofAdd_eq_one] at hexp
  exact hN k hk (by simpa [ρ, hexp] using hj.symm)

/-- The factor `ℤ²` is abelian, so it centralizes each of its elements. -/
private theorem range_inl_le_centralizer (v : Multiplicative (ℤ × ℤ)) :
    (inl : Multiplicative (ℤ × ℤ) →* IntSqCoprodInt).range ≤ centralizer {inl v} := by
  rintro _ ⟨w, rfl⟩
  exact mem_centralizer_singleton_iff.2 ((Commute.all w v).map inl).eq

/-- The centralizer in `ℤ² ∗ ℤ` of a nontrivial element of the factor `ℤ²`, for instance of
`(1, 0)`, is the factor `ℤ²`. -/
theorem centralizer_inl_eq_range_inl {v : Multiplicative (ℤ × ℤ)} (hv : v ≠ 1) :
    centralizer {(inl v : IntSqCoprodInt)} =
      (inl : Multiplicative (ℤ × ℤ) →* IntSqCoprodInt).range := by
  refine le_antisymm (fun g hg => ⟨fst g, ?_⟩) (range_inl_le_centralizer v)
  have hc : Commute ((inl (fst g))⁻¹ * g) (inl v) :=
    ((Commute.all _ _).map inl).inv_left.mul_left (mem_centralizer_singleton_iff.1 hg)
  exact inv_mul_eq_one.1 (eq_one_of_commute_of_fst_eq_one hv hc (by simp))

/-- The centralizer in `ℤ² ∗ ℤ` of an element of the factor `ℤ²` is not cyclic, although
`ℤ² ∗ ℤ` is fully residually free. -/
theorem not_isCyclic_centralizer_inl (v : Multiplicative (ℤ × ℤ)) :
    ¬IsCyclic (centralizer {(inl v : IntSqCoprodInt)}) := fun _ =>
  -- The centralizer contains the factor `ℤ²`, which is not cyclic.
  have := Subgroup.isCyclic_of_le (range_inl_le_centralizer v)
  not_isAddCyclic_prod_of_infinite_nontrivial ℤ ℤ <| isCyclic_multiplicative_iff.1 <|
    (MonoidHom.ofInjective inl_injective).isCyclic.2 this

/-- Distinct elements of the factor `ℤ²`, such as `(1, 0)` and `(0, 1)`, are not conjugate in
`ℤ² ∗ ℤ`. -/
theorem not_isConj_inl_of_ne {u v : Multiplicative (ℤ × ℤ)} (h : u ≠ v) :
    ¬IsConj (inl u : IntSqCoprodInt) (inl v) := by
  simpa

/-- Over `ℤ² ∗ ℤ`, the solutions of the commutator equation `[x, v] = 1`, for a nontrivial `v` in
the factor `ℤ²` such as `(1, 0)`, are exactly the points whose `x`-coordinate lies in `ℤ²`. -/
theorem V_singleton_commutatorElement_inl {X : Type*} (x : X) {v : Multiplicative (ℤ × ℤ)}
    (hv : v ≠ 1) :
    GroupAlgGeom.V (.id IntSqCoprodInt)
        {⁅(inr (FreeGroup.of x) : GroupAlgGeom.GX IntSqCoprodInt X), inl (inl v)⁆} =
      {u | u x ∈ (inl : Multiplicative (ℤ × ℤ) →* IntSqCoprodInt).range} := by
  rw [GroupAlgGeom.V_singleton_commutatorElement, MonoidHom.id_apply,
    centralizer_inl_eq_range_inl hv]

end IntSqCoprodInt

end TauCeti.LimitGroup
