/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BigPowers
public import TauCeti.GroupTheory.PushoutI
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree

/-!
# Extensions of centralizers are discriminated by the base group

Let `G` be a nonabelian CSA group with the big powers property, for example a nonabelian fully
residually free group, and let `u ≠ 1`. The retractions `ξ_k : G(u, ℤ) →* G`, `t ↦ u ^ k`, of the
extension of the centralizer of `u` discriminate `G(u, ℤ)` by `G`: every nonidentity element
survives under `ξ_k` for all large `k`, so any finitely many of them survive under one `ξ_k`.
Consequently the extension of a centralizer of a nonidentity element in a nonabelian fully
residually free group is again fully residually free.

The proof writes an element of the amalgam `G(u, ℤ) = G ∗_{C_G(u)} (C_G(u) × ℤ)` in reduced form
`a₀ * t ^ m₀ * a₁ * ⋯ * t ^ m_r * a_{r+1}` with every `mᵢ ≠ 0` and the intermediate `aᵢ` outside
`C_G(u)` (`CentralizerExt.exists_eq_of_mul_prod_map_zpow_t_mul_of`), using Mathlib's normal form
for amalgamated products, and then applies the big powers property with coefficients
(`Group.IsBP.exists_forall_mul_prod_map_zpow_mul_ne_one`) to its images
`a₀ * u ^ (k * m₀) * a₁ * ⋯`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.exists_eq_of_mul_prod_map_zpow_t_mul_of`: reduced forms in
  `G(u, ℤ)`.
* `TauCeti.LimitGroup.CentralizerExt.exists_forall_retraction_ne_one`: a nonidentity element of
  `G(u, ℤ)` survives under every retraction `t ↦ u ^ k` with `k` large enough.
* `TauCeti.LimitGroup.CentralizerExt.isDiscriminatedBy`: `G(u, ℤ)` is `G`-discriminated by `G`.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.centralizerExt`: extending the centralizer of a
  nonidentity element of a nonabelian fully residually free group gives a fully residually free
  group.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II*,
  J. Algebra 200 (1998), §0, Lemma 2 and Theorem 1.
* G. Baumslag, *On generalised free products*, Math. Z. 78 (1962), 423–438.
-/

public section

open Subgroup Group TauCeti.GroupAlgGeom

universe u

namespace TauCeti.LimitGroup

namespace CentralizerExt

variable {G : Type u} [Group G] {u : G}

/-- A letter `(c, v)` of the second factor `C_G(u) × ℤ` of `G(u, ℤ)` is `c * t ^ v`. -/
private theorem of_true_apply (c : centralizer {u}) (v : Fin 1 → Multiplicative ℤ) :
    Monoid.PushoutI.of (φ := centralizerExtMap u 1) true (c, v) =
      of (c : G) * t 0 ^ (v 0).toAdd := by
  have hv : ((c, v) : centralizer {u} × (Fin 1 → Multiplicative ℤ)) =
      (c, 1) * (1, Pi.mulSingle 0 (.ofAdd 1)) ^ (v 0).toAdd := by
    refine Prod.ext (by simp) (funext fun i => ?_)
    rw [Subsingleton.elim i 0]
    simp [← ofAdd_zsmul]
  rw [hv, map_mul, map_zpow, of_true_inl, t_def]

/-- A reduced word of the amalgam `G(u, ℤ)` evaluates to `a₀ * t ^ m₀ * a₁ * ⋯ * t ^ m_r * a_{r+1}`
with nonzero exponents and intermediate coefficients outside `C_G(u)`. The last three conjuncts
record how the leading coefficient depends on the first letter, which makes the induction go
through: letters `g ∈ G \ C_G(u)` are absorbed into the leading coefficient, and letters
`(c, v)` of `C_G(u) × ℤ` contribute `c * t ^ v`. -/
private theorem exists_eq_of_reduced (v : Monoid.CoprodI.Word (CentralizerExtFactor u 1))
    (hv : Monoid.PushoutI.Reduced (centralizerExtMap u 1) v) :
    ∃ (a : G) (l : List (ℤ × G)), (∀ p ∈ l, p.1 ≠ 0) ∧
      (∀ p ∈ l.dropLast, p.2 ∉ centralizer {u}) ∧
      Monoid.PushoutI.ofCoprodI v.prod = of a * (l.map fun p => t 0 ^ p.1 * of p.2).prod ∧
      (v.fstIdx = none → l = []) ∧ (v.fstIdx = some true → a ∈ centralizer {u}) ∧
      (v.fstIdx = some false → l ≠ [] → a ∉ centralizer {u}) := by
  induction v using Monoid.CoprodI.Word.consRecOn with
  | empty => exact ⟨1, [], by simp, by simp, by simp [Monoid.CoprodI.Word.prod]⟩
  | cons i g v hidx hg1 ih =>
    obtain ⟨a, l, hm, hC, hprod, hnone, htrue, hfalse⟩ :=
      ih fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hg := hv ⟨i, g⟩ List.mem_cons_self
    have hprod' : Monoid.PushoutI.ofCoprodI (φ := centralizerExtMap u 1)
        (Monoid.CoprodI.Word.cons g v hidx hg1).prod =
        Monoid.PushoutI.of i g * Monoid.PushoutI.ofCoprodI v.prod := by
      rw [Monoid.CoprodI.Word.prod_cons, map_mul, Monoid.PushoutI.ofCoprodI_of]
    cases i with
    | false =>
      obtain ⟨g, rfl⟩ : ∃ g' : G, g' = g := ⟨g, rfl⟩
      have hgC : g ∉ centralizer {u} := by simpa using hg
      refine ⟨g * a, l, hm, hC, ?_, by simp, by simp, fun _ hl hga => ?_⟩
      · rw [hprod', hprod, ← mul_assoc, map_mul, of_def]
      · match hv' : v.fstIdx, hidx with
        | none, _ => exact hl (hnone hv')
        | some true, _ => exact hgC ((mul_mem_cancel_right (htrue hv')).1 hga)
    | true =>
      obtain ⟨c, vv⟩ := g
      have hvv : (vv 0).toAdd ≠ 0 := by
        rw [centralizerExtMap_true] at hg
        intro h0
        have h1 : vv 0 = 1 := by simpa using h0
        -- `MonoidHom.inl _ _ c` is `(c, 1)` by definition; `simp` cannot see this through the
        -- instance on the `Bool`-indexed factor.
        refine hg ⟨c, Prod.ext rfl (funext fun i => ?_)⟩
        rw [Subsingleton.elim i 0]
        exact h1.symm
      refine ⟨c, ((vv 0).toAdd, a) :: l, ?_, ?_, ?_, by simp, fun _ => c.2, by simp⟩
      · simpa [hvv] using hm
      · rcases l with _ | ⟨q, l⟩
        · simp
        · have ha : a ∉ centralizer {u} := by
            match hv' : v.fstIdx, hidx with
            | none, _ => exact absurd (hnone hv') (List.cons_ne_nil _ _)
            | some false, _ => exact hfalse hv' (List.cons_ne_nil _ _)
          simpa [List.dropLast_cons_cons, ha] using hC
      · rw [hprod', hprod, of_true_apply]
        simp [mul_assoc]

/-- **Reduced forms in `G(u, ℤ)`.** Every element of the extension of a centralizer by `ℤ` is
`a₀ * t ^ m₀ * a₁ * ⋯ * t ^ m_r * a_{r+1}` with every exponent `mᵢ ≠ 0` and every intermediate
coefficient `a₁, …, a_r` outside `C_G(u)`. -/
theorem exists_eq_of_mul_prod_map_zpow_t_mul_of (x : CentralizerExt u 1) :
    ∃ (a : G) (l : List (ℤ × G)), (∀ p ∈ l, p.1 ≠ 0) ∧
      (∀ p ∈ l.dropLast, p.2 ∉ centralizer {u}) ∧
      x = of a * (l.map fun p => t 0 ^ p.1 * of p.2).prod := by
  obtain ⟨h, w, hw, rfl⟩ :=
    Monoid.PushoutI.exists_reduced_eq_base_mul_ofCoprodI_prod (centralizerExtMap_injective u 1) x
  obtain ⟨a, l, hm, hC, hprod, -⟩ := exists_eq_of_reduced w hw
  refine ⟨(h : G) * a, l, hm, hC, ?_⟩
  rw [hprod, map_mul, mul_assoc, ← Monoid.PushoutI.of_apply_eq_base _ false, of_def,
    centralizerExtMap_false, coe_subtype]

/-- The retraction `t ↦ u ^ k` sends `a₀ * t ^ m₀ * a₁ * ⋯` to `a₀ * u ^ (k * m₀) * a₁ * ⋯`. -/
private theorem retraction_of_mul_prod (k : ℤ) (a : G) (l : List (ℤ × G)) :
    retraction (fun _ => k)
        (of a * (l.map fun p => t 0 ^ p.1 * of p.2).prod : CentralizerExt u 1) =
      a * (l.map fun p => u ^ (k * p.1) * p.2).prod := by
  simp [map_list_prod, List.map_map, Function.comp_def, zpow_mul]

/-- Let `G` be a nonabelian CSA group with the big powers property and `u ≠ 1`. Every nonidentity
element of `G(u, ℤ)` survives under the retraction `t ↦ u ^ k` for every large enough `k`. -/
theorem exists_forall_retraction_ne_one (hBP : IsBP G) (hG : IsCSA G)
    (hab : ¬IsMulCommutative G) (hu : u ≠ 1) {x : CentralizerExt u 1} (hx : x ≠ 1) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → retraction (fun _ => (k : ℤ)) x ≠ 1 := by
  obtain ⟨a, l, hm, hC, rfl⟩ := exists_eq_of_mul_prod_map_zpow_t_mul_of x
  simp_rw [retraction_of_mul_prod]
  rcases eq_or_ne l [] with rfl | hl
  · refine ⟨0, fun _ _ h => hx ?_⟩
    simp only [List.map_nil, List.prod_nil, mul_one] at h ⊢
    rw [h, map_one]
  · exact hBP.exists_forall_mul_prod_map_zpow_mul_ne_one hG hab hu a hl hm hC

/-- **Extensions of centralizers are discriminated by the base group.** If `G` is a nonabelian CSA
group with the big powers property and `u ≠ 1`, then `G(u, ℤ)` is discriminated by `G` over `G`:
any finitely many nonidentity elements survive under one retraction `t ↦ u ^ k`. -/
theorem isDiscriminatedBy (hBP : IsBP G) (hG : IsCSA G) (hab : ¬IsMulCommutative G)
    (hu : u ≠ 1) : IsDiscriminatedBy (of : G →* CentralizerExt u 1) (MonoidHom.id G) := by
  refine (isDiscriminatedBy_def _ _).2 fun s hs => ?_
  choose! N hN using fun x (hx : x ∈ s) =>
    exists_forall_retraction_ne_one hBP hG hab hu (hs x hx)
  exact ⟨⟨retraction fun _ => ((s.sup N : ℕ) : ℤ), fun g => by simp⟩,
    fun x hx => hN x hx _ (Finset.le_sup hx)⟩

end CentralizerExt

variable {G : Type u} [Group G]

/-- Extending the centralizer of a nonidentity element of a nonabelian fully residually free group
by `ℤ` gives a fully residually free group. -/
theorem IsFullyResiduallyFree.centralizerExt (h : IsFullyResiduallyFree G)
    (hab : ¬IsMulCommutative G) {u : G} (hu : u ≠ 1) :
    IsFullyResiduallyFree (CentralizerExt u 1) := by
  classical
  refine isFullyResiduallyFree_def.2 fun s hs => ?_
  obtain ⟨φ, hφ⟩ := (isDiscriminatedBy_def _ _).1
    (CentralizerExt.isDiscriminatedBy h.isBP h.isCSA hab hu) s hs
  obtain ⟨ι, ψ, hψ⟩ := isFullyResiduallyFree_def.1 h (s.image φ) (by simpa using hφ)
  exact ⟨ι, ψ.comp (φ : CentralizerExt u 1 →* G),
    fun x hx => hψ _ (Finset.mem_image_of_mem _ hx)⟩

/-- Extending the centralizer of a nonidentity element of a nonabelian free group by `ℤ` gives a
fully residually free group; for example `⟨a, b, t | [a, t] = 1⟩`. -/
theorem isFullyResiduallyFree_centralizerExt_freeGroup {α : Type u} [Nontrivial α]
    {u : FreeGroup α} (hu : u ≠ 1) : IsFullyResiduallyFree (CentralizerExt u 1) :=
  isFullyResiduallyFree_of_isFreeGroup.centralizerExt
    (fun h => not_subsingleton α (FreeGroup.isMulCommutative_iff_subsingleton.1 h)) hu


end TauCeti.LimitGroup
