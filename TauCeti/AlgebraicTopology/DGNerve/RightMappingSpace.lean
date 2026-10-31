/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Basic
public import TauCeti.AlgebraicTopology.DoldKan.SimplexChainMap
public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
import TauCeti.Data.Finset.Basic

/-!
# Right mapping spaces of the differential graded nerve

For objects `X` and `Y` of a differential graded category `C`, the right mapping space
`Hom^R_{N_dg(C)}(X, Y)` is computed by the Hom complex `Hom_C(X, Y)`: it is isomorphic to the
simplicial set `(dgHomComplex R X Y).simplexChainMaps` of chain maps from the normalized chains of
the standard simplices to the good truncation `τ_{≥ 0} Hom_C(X, Y)`. Such chain maps are the
simplices of the Dold–Kan construction on `τ_{≥ 0} Hom_C(X, Y)` in its normalized-chain
description, so this identifies the mapping spaces of the differential graded nerve, and not just
its homotopy category, in terms of the Hom complexes.

An `n`-simplex of `Hom^R_{N_dg(C)}(X, Y)` is an `(n + 1)`-simplex of `N_dg(C)` whose first `n + 1`
vertices span the constant simplex at `X` and whose last vertex is `Y`
(`TauCeti.dgNerve.mem_rightMappingSpace_iff`): its coherences between the first `n + 1` vertices
are identities and zeros. Its remaining coherences `f_{J ∪ {n + 1}}`, for nonempty `J ⊆ [n]`, have
degree `1 - #J`, and the dg nerve equation for them reduces to

`d f_{J ∪ {n + 1}} = (-1) ^ #J • ∑_{j ∈ J} (-1) ^ #{s ∈ J | s < j} • f_{J \ {j} ∪ {n + 1}}`,

since all composites through the first `n + 1` vertices vanish except the one through the first
vertex of `J`, which composes with an identity. Multiplying `f_{J ∪ {n + 1}}` by the sign
`(-1) ^ (#J - 1 choose 2)` removes the factor `(-1) ^ #J`, giving exactly the equation of a chain
map from the normalized chains of `Δ[n]`.

## Main definitions and results

* `TauCeti.dgNerve.mem_rightMappingSpace_iff`: the simplices of `Hom^R_{N_dg(C)}(X, Y)`.
* `TauCeti.dgNerve.rightMappingSpaceEquiv`: the `n`-simplices of `Hom^R_{N_dg(C)}(X, Y)` are the
  chain maps from the normalized chains of `Δ[n]` to `τ_{≥ 0} Hom_C(X, Y)`.
* `TauCeti.dgNerve.rightMappingSpaceIso`: the resulting isomorphism of simplicial sets.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Remark 1.3.1.12.
-/

public section

open CategoryTheory Finset Opposite Simplicial

namespace TauCeti

universe v u

namespace DGNerve

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-! ### Transport of homogeneous morphisms -/

/-- Transport of a homogeneous morphism along equalities of its source, target and degree. -/
private noncomputable def dgCast {X X' Y Y' : C} {d d' : ℤ} (hX : X = X') (hY : Y = Y')
    (hd : d = d') : DGHom R d X Y →ₗ[R] DGHom R d' X' Y' := by
  subst hX hY hd
  exact LinearMap.id

private theorem dgCast_eq_iff_heq {X X' Y Y' : C} {d d' : ℤ} (hX : X = X') (hY : Y = Y')
    (hd : d = d') (f : DGHom R d X Y) (g : DGHom R d' X' Y') :
    dgCast hX hY hd f = g ↔ f ≍ g := by
  subst hX hY hd
  exact heq_iff_eq.symm

private theorem dgCast_heq {X X' Y Y' : C} {d d' : ℤ} (hX : X = X') (hY : Y = Y') (hd : d = d')
    (f : DGHom R d X Y) : dgCast hX hY hd f ≍ f :=
  ((dgCast_eq_iff_heq hX hY hd f _).1 rfl).symm

private theorem dgCast_dgCast {X X' X'' Y Y' Y'' : C} {d d' d'' : ℤ} (hX : X = X')
    (hY : Y = Y') (hd : d = d') (hX' : X' = X'') (hY' : Y' = Y'') (hd' : d' = d'')
    (f : DGHom R d X Y) :
    dgCast hX' hY' hd' (dgCast hX hY hd f) =
      dgCast (hX.trans hX') (hY.trans hY') (hd.trans hd') f := by
  subst hX hY hd hX' hY' hd'
  rfl

private theorem dgCast_units_smul {X X' Y Y' : C} {d d' : ℤ} (hX : X = X') (hY : Y = Y')
    (hd : d = d') (u : ℤˣ) (f : DGHom R d X Y) :
    dgCast hX hY hd (u • f) = u • dgCast hX hY hd f := by
  subst hX hY hd
  rfl

private theorem dgDifferential_units_smul {X Y : C} {d : ℤ} (u : ℤˣ) (f : DGHom R d X Y) :
    dgDifferential R d (u • f) = u • dgDifferential R d f := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private theorem dgDifferential_dgCast {X X' Y Y' : C} {d : ℤ} (hX : X = X') (hY : Y = Y')
    (f : DGHom R d X Y) :
    dgDifferential R d (dgCast hX hY rfl f) = dgCast hX hY rfl (dgDifferential R d f) := by
  subst hX hY
  rfl

private theorem dgCast_injective {X X' Y Y' : C} {d d' : ℤ} (hX : X = X') (hY : Y = Y')
    (hd : d = d') : Function.Injective (dgCast (R := R) hX hY hd) := by
  subst hX hY hd
  exact fun _ _ h ↦ h

private theorem dgId_heq {X X' : C} (h : X = X') : dgId R X ≍ dgId R X' := by
  subst h
  rfl

private theorem dgDifferential_eq_zero_of_heq_dgId {A B X : C} {d : ℤ} {a : DGHom R d A B}
    (hA : A = X) (hB : B = X) (hd : d = 0) (ha : a ≍ dgId R X) : dgDifferential R d a = 0 := by
  subst hA hB hd
  rw [eq_of_heq ha]
  exact dgDifferential_dgId R _

private theorem dgComp_heq_dgId {A B Z X : C} {p q r : ℤ} {a : DGHom R p A B}
    {b : DGHom R q B Z} (e : p + q = r) (hA : A = X) (hB : B = X) (hZ : Z = X) (hp : p = 0)
    (hq : q = 0) (ha : a ≍ dgId R X) (hb : b ≍ dgId R X) : dgComp R a b e ≍ dgId R X := by
  subst hA hB hZ hp hq e
  rw [eq_of_heq ha, eq_of_heq hb]
  exact heq_of_eq (dgId_dgComp R _)

/-- A zero morphism between objects equal to `X` and `X'` is heterogeneously equal to zero. -/
private theorem zero_heq_zero {X X' Y Y' : C} {d : ℤ} (hX : X = X') (hY : Y = Y') :
    (0 : DGHom R d X Y) ≍ (0 : DGHom R d X' Y') := by
  subst hX hY
  rfl

/-- Composing with a morphism heterogeneously equal to an identity does nothing, up to
transport. -/
private theorem dgCast_dgComp_of_heq_dgId {A B Z X Z' : C} {p q r r' : ℤ}
    {a : DGHom R p A B} (g : DGHom R q B Z) (e : p + q = r) (hA : A = X) (hB : B = X)
    (hZ : Z = Z') (hp : p = 0) (ha : a ≍ dgId R X) (hr : r = r') (hq : q = r') :
    dgCast hA hZ hr (dgComp R a g e) = dgCast hB hZ hq g := by
  subst hA hB hZ hp hr hq
  obtain rfl := eq_of_heq ha
  exact (dgId_dgComp R g)

/-! ### Last-column coherences -/

/-- The sign `(-1) ^ (r choose 2)` by which the last-column coherences of a simplex of a right
mapping space differ from the values of the corresponding chain map. -/
private noncomputable abbrev twist (r : ℕ) : ℤˣ := ((r.choose 2 : ℕ) : ℤ).negOnePow

private theorem twist_succ (r : ℕ) : twist (r + 1) = twist r * (r : ℤ).negOnePow := by
  simp only [twist, Nat.choose_succ_succ', Nat.choose_one_right, Nat.cast_add,
    Int.negOnePow_add, mul_comm]

private theorem twist_mul_self (r : ℕ) : twist r * twist r = 1 :=
  Int.units_mul_self _

private theorem twist_face {r p q : ℕ} (h : q + p = r + 1) :
    ((p + 1 : ℕ) : ℤ).negOnePow * twist r = twist (r + 1) * (q : ℤ).negOnePow := by
  simp only [twist, Nat.choose_succ_succ', Nat.choose_one_right, ← Int.negOnePow_add,
    Int.negOnePow_eq_iff]
  exact ⟨(p : ℤ) - r, by push_cast; omega⟩

private theorem twist_eq_neg (r : ℕ) :
    twist r = -(twist (r + 1) * ((r + 1 : ℕ) : ℤ).negOnePow) := by
  rw [twist_succ, mul_assoc, ← Int.negOnePow_add, ← mul_neg, ← Int.negOnePow_succ,
    Int.negOnePow_even _ ⟨r + 1, by push_cast; ring⟩, mul_one]

private theorem notMem_of_subset_Ioi {n : ℕ} {i : Fin (n + 1)} {S : Finset (Fin (n + 1))}
    (hS : S ⊆ Ioi i) : i ∉ S :=
  fun h ↦ lt_irrefl i (mem_Ioi.1 (hS h))

/-- The alternating sum over the faces of `insert i S`, for `S` above `i`, of values `v` that are
twisted last-column values `G`: the face omitting `i` contributes the term through the first
vertex of `S`, and the other faces the terms omitting a vertex of `S`. -/
private theorem sum_faces_insert {n : ℕ} {M : Type*} [AddCommGroup M]
    (v : Finset (Fin (n + 1)) → M) (G : Fin (n + 1) → Finset (Fin (n + 1)) → M) (hv₀ : v ∅ = 0)
    (hvG : ∀ a T, T ⊆ Ioi a → v (insert a T) = twist #T • G a T) {i : Fin (n + 1)}
    {S : Finset (Fin (n + 1))} (hS : S ⊆ Ioi i) :
    ∑ j ∈ insert i S, (#{s ∈ insert i S | s < j} : ℤ).negOnePow • v ((insert i S).erase j) =
      twist #S • (∑ t ∈ S, (#{s ∈ S | t ≤ s} : ℤ).negOnePow • G i (S.erase t) -
        if h : S.Nonempty then (#S : ℤ).negOnePow • G (S.min' h) (S.erase (S.min' h)) else 0) := by
  have hi : i ∉ S := notMem_of_subset_Ioi hS
  have h₀ : {s ∈ insert i S | s < i} = ∅ :=
    filter_eq_empty_iff.2 fun s hs ↦ by
      rcases mem_insert.1 hs with rfl | hs
      · exact lt_irrefl s
      · exact (mem_Ioi.1 (hS hs)).not_gt
  rw [sum_insert hi, erase_insert hi, h₀, card_empty, Nat.cast_zero, Int.negOnePow_zero, one_smul]
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [hv₀]
  obtain ⟨r, hr⟩ : ∃ r, #S = r + 1 := ⟨#S - 1, by have := hne.card_pos; omega⟩
  have hmin : v S = twist r • G (S.min' hne) (S.erase (S.min' hne)) := by
    conv_lhs => rw [← insert_erase (min'_mem S hne)]
    rw [hvG _ _ fun s hs ↦ mem_Ioi.2 (lt_of_le_of_ne (min'_le _ _ (mem_of_mem_erase hs))
      (ne_of_mem_erase hs).symm), card_erase_of_mem (min'_mem S hne), hr, Nat.add_sub_cancel]
  have hface : ∀ t ∈ S, (#{s ∈ insert i S | s < t} : ℤ).negOnePow • v ((insert i S).erase t) =
      twist #S • ((#{s ∈ S | t ≤ s} : ℤ).negOnePow • G i (S.erase t)) := fun t ht ↦ by
    have hit : i < t := mem_Ioi.1 (hS ht)
    have hcount : #{s ∈ S | t ≤ s} + #{s ∈ S | s < t} = r + 1 := by
      have := card_filter_add_card_filter_not (s := S) (fun s ↦ t ≤ s)
      simp only [not_le] at this
      omega
    rw [erase_insert_of_ne hit.ne, hvG _ _ ((erase_subset _ _).trans hS),
      card_erase_of_mem ht, hr, Nat.add_sub_cancel, filter_insert, ite_eq_left hit,
      card_insert_of_notMem (by simp [hi]), smul_smul, smul_smul, twist_face hcount]
  rw [hmin, sum_congr rfl hface, ← smul_sum, dite_eq_left hne, smul_sub, add_comm,
    sub_eq_add_neg, hr, smul_smul, ← Units.neg_smul, ← twist_eq_neg]

private theorem map_castSucc_subset_Ioo {n : ℕ} {i : Fin (n + 1)} {S : Finset (Fin (n + 1))}
    (hS : S ⊆ Ioi i) : S.map Fin.castSuccEmb ⊆ Ioo i.castSucc (Fin.last (n + 1)) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := mem_map.1 hs
  exact mem_Ioo.2 ⟨Fin.castSucc_lt_castSucc_iff.2 (mem_Ioi.1 (hS ht)), Fin.castSucc_lt_last t⟩

private theorem subset_Ioo_of_map_castSucc {n : ℕ} {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))}
    (hS : S.map Fin.castSuccEmb ⊆ Ioo i.castSucc j.castSucc) : S ⊆ Ioo i j := fun s hs ↦ by
  simpa [Fin.castSucc_lt_castSucc_iff] using hS (mem_map_of_mem Fin.castSuccEmb hs)

private theorem subset_Ioi_of_map_castSucc {n : ℕ} {i : Fin (n + 1)} {j : Fin (n + 2)}
    {S : Finset (Fin (n + 1))} (hS : S.map Fin.castSuccEmb ⊆ Ioo i.castSucc j) : S ⊆ Ioi i :=
  fun _ hs ↦ mem_Ioi.2 (Fin.castSucc_lt_castSucc_iff.1 (mem_Ioo.1 (hS (mem_map_of_mem _ hs))).1)

/-- A set of vertices of `[n + 1]` strictly below a vertex consists of images of vertices of
`[n]`. -/
private theorem exists_map_castSucc_eq {n : ℕ} {S : Finset (Fin (n + 2))} {i j : Fin (n + 2)}
    (hS : S ⊆ Ioo i j) : ∃ S₀ : Finset (Fin (n + 1)), S₀.map Fin.castSuccEmb = S := by
  refine ⟨S.preimage Fin.castSucc (Fin.castSucc_injective _).injOn, ?_⟩
  ext s
  simp only [mem_map, mem_preimage, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨s₀, hs₀, rfl⟩
    exact hs₀
  · intro hs
    obtain ⟨s₀, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt (mem_Ioo.1 (hS hs)).2)
    exact ⟨s₀, hs, rfl⟩

variable {n : ℕ} {obj : Fin (n + 2) → C} {X Y : C}
  (hX : ∀ i : Fin (n + 1), obj i.castSucc = X) (hY : obj (Fin.last (n + 1)) = Y)

/-- The coherence from the vertex `i` through the vertices `S` to the last vertex, transported to
a morphism `X ⟶ Y`; zero when `S` is not above `i` or the degree is not `-#S`. -/
private noncomputable def lastCol (f : Coherences R obj) (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (d : ℤ) : DGHom R d X Y :=
  if h : S ⊆ Ioi i ∧ d + #S = 0 then
    dgCast (hX i) hY rfl (f i.castSucc (Fin.last (n + 1)) (S.map Fin.castSuccEmb) d
      (Fin.castSucc_lt_last i).le (map_castSucc_subset_Ioo h.1) (by rw [card_map]; exact h.2))
  else 0

private theorem lastCol_eq (f : Coherences R obj) {i : Fin (n + 1)} {S : Finset (Fin (n + 1))}
    {d d' : ℤ} (hS : S ⊆ Ioi i) {S' : Finset (Fin (n + 2))} (hS' : S' = S.map Fin.castSuccEmb)
    (h₁ : i.castSucc ≤ Fin.last (n + 1)) (h₂ : S' ⊆ Ioo i.castSucc (Fin.last (n + 1)))
    (h₃ : d + #S' = 0) (hd : d = d') :
    dgCast (hX i) hY hd (f i.castSucc (Fin.last (n + 1)) S' d h₁ h₂ h₃) =
      lastCol hX hY f i S d' := by
  subst hS' hd
  rw [lastCol, dite_eq_left ⟨hS, by rwa [card_map] at h₃⟩]

private theorem lastCol_eq_zero (f : Coherences R obj) {i : Fin (n + 1)}
    {S : Finset (Fin (n + 1))} {d : ℤ} (h : d + #S ≠ 0) : lastCol hX hY f i S d = 0 :=
  dite_eq_right fun h' ↦ h h'.2

/-- The hypotheses on coherences `f` on `obj` saying that their restriction to the first `n + 1`
vertices is that of the constant simplex at `X`: identities and zeros. -/
private def IsConstInit (f : Coherences R obj) (X : C) : Prop :=
  (∀ i j S d hij hS hd, j ≠ Fin.last (n + 1) → S.Nonempty → f i j S d hij hS hd = 0) ∧
    ∀ i j d hij hS hd, j ≠ Fin.last (n + 1) → f i j ∅ d hij hS hd ≍ dgId R X

/-- The term at a vertex `t` of the right-hand side of the dg nerve equation for a last-column
coherence. -/
private theorem dgCast_boundary_term (f : Coherences R obj) (hf : IsConstInit f X)
    {i : Fin (n + 1)} {S : Finset (Fin (n + 1))} (hS : S ⊆ Ioi i) {d : ℤ}
    (hij : i.castSucc ≤ Fin.last (n + 1))
    (hS' : S.map Fin.castSuccEmb ⊆ Ioo i.castSucc (Fin.last (n + 1)))
    (hd : d + #(S.map Fin.castSuccEmb) = 0) {t : Fin (n + 1)} (ht : t ∈ S)
    (ht' : t.castSucc ∈ S.map Fin.castSuccEmb) :
    dgCast (hX i) hY rfl
        ((#{s ∈ S.map Fin.castSuccEmb | t.castSucc ≤ s} : ℤ).negOnePow •
          (f i.castSucc (Fin.last (n + 1)) ((S.map Fin.castSuccEmb).erase t.castSucc) (d + 1)
            hij ((erase_subset _ _).trans hS') (add_one_add_card_erase_eq_zero ht' hd) -
          (#{s ∈ S.map Fin.castSuccEmb | s < t.castSucc} *
              #{s ∈ S.map Fin.castSuccEmb | t.castSucc < s} : ℤ).negOnePow •
            dgComp R
              (f i.castSucc t.castSucc {s ∈ S.map Fin.castSuccEmb | s < t.castSucc} _
                (mem_Ioo.1 (hS' ht')).1.le (filter_lt_subset_Ioo hS') (neg_add_cancel _))
              (f t.castSucc (Fin.last (n + 1)) {s ∈ S.map Fin.castSuccEmb | t.castSucc < s} _
                (mem_Ioo.1 (hS' ht')).2.le (filter_gt_subset_Ioo hS') (neg_add_cancel _))
              (neg_card_filter_lt_add_neg_card_filter_gt ht' hd))) =
      (#{s ∈ S | t ≤ s} : ℤ).negOnePow • (lastCol hX hY f i (S.erase t) (d + 1) -
        if {s ∈ S | s < t} = ∅ then lastCol hX hY f t (S.erase t) (d + 1) else 0) := by
  have hle : #{s ∈ S.map Fin.castSuccEmb | t.castSucc ≤ s} = #{s ∈ S | t ≤ s} := by
    rw [filter_map, card_map]
    simp [Function.comp_def]
  have hlt : {s ∈ S.map Fin.castSuccEmb | s < t.castSucc} = {s ∈ S | s < t}.map
      Fin.castSuccEmb := by
    rw [filter_map]
    simp [Function.comp_def]
  rw [dgCast_units_smul, map_sub, hle, lastCol_eq hX hY f ((erase_subset _ _).trans hS)
    (by rw [map_erase]; rfl) _ _ _ rfl]
  congr 2
  by_cases hmin : {s ∈ S | s < t} = ∅
  · rw [ite_eq_left hmin]
    -- The only composite term: the identity of `X` followed by a last-column coherence.
    have hgt : {s ∈ S.map Fin.castSuccEmb | t.castSucc < s} = (S.erase t).map
        Fin.castSuccEmb := by
      rw [filter_map]
      congr 1
      ext s
      simp only [mem_filter, mem_erase, Function.comp_apply, Fin.castSuccEmb_apply,
        Fin.castSucc_lt_castSucc_iff]
      constructor
      · rintro ⟨hs, hts⟩
        exact ⟨hts.ne', hs⟩
      · rintro ⟨hst, hs⟩
        exact ⟨hs, lt_of_le_of_ne (not_lt.1 fun hst' ↦ (filter_eq_empty_iff.1 hmin) hs hst')
          (Ne.symm hst)⟩
    have hempty : {s ∈ S.map Fin.castSuccEmb | s < t.castSucc} = ∅ := by
      rw [hlt, hmin, map_empty]
    have hcard : #{s ∈ S.map Fin.castSuccEmb | s < t.castSucc} = 0 := by
      rw [hempty, card_empty]
    have hpos := card_pos.2 ⟨t, ht⟩
    simp only [hcard, Nat.cast_zero, zero_mul, Int.negOnePow_zero, one_smul]
    have hid := hf.2 i.castSucc t.castSucc (-(#{s ∈ S.map Fin.castSuccEmb | s < t.castSucc} : ℤ))
      (mem_Ioo.1 (hS' ht')).1.le (empty_subset _) (by rw [hcard]; simp) (Fin.castSucc_ne_last t)
    have hq : -(#{s ∈ S.map Fin.castSuccEmb | t.castSucc < s} : ℤ) = d + 1 := by
      rw [hgt, card_map, card_erase_of_mem ht]
      rw [card_map] at hd
      push_cast [Nat.cast_sub hpos]
      omega
    rw [dgCast_dgComp_of_heq_dgId _ _ (hX i) (hX t) hY (by rw [hcard]; rfl)
      ((heq_of_eq (Coherences.congr f hempty)).trans hid) rfl hq]
    exact lastCol_eq hX hY f (fun s hs ↦ mem_Ioi.2 (lt_of_le_of_ne
      (not_lt.1 fun hst ↦ (filter_eq_empty_iff.1 hmin) (mem_of_mem_erase hs) hst)
      (ne_of_mem_erase hs).symm)) hgt _ _ _ _
  · rw [ite_eq_right hmin]
    have hne : {s ∈ S.map Fin.castSuccEmb | s < t.castSucc}.Nonempty := by
      rw [hlt]
      exact (nonempty_iff_ne_empty.2 hmin).map
    rw [hf.1 _ _ _ _ _ _ _ (Fin.castSucc_ne_last t) hne, zero_dgComp, smul_zero, map_zero]

/-- For coherences whose restriction to the first `n + 1` vertices is that of a constant simplex,
the right-hand side of the dg nerve equation for a last-column coherence is a combination of
last-column coherences: the composites through the first `n + 1` vertices vanish, except the one
through the first vertex of `S`, which composes with an identity. -/
private theorem dgCast_boundary_last (f : Coherences R obj) (hf : IsConstInit f X)
    {i : Fin (n + 1)} {S : Finset (Fin (n + 1))} (hS : S ⊆ Ioi i) {d : ℤ}
    (hij : i.castSucc ≤ Fin.last (n + 1))
    (hS' : S.map Fin.castSuccEmb ⊆ Ioo i.castSucc (Fin.last (n + 1)))
    (hd : d + #(S.map Fin.castSuccEmb) = 0) :
    dgCast (hX i) hY rfl (boundary R f i.castSucc (Fin.last (n + 1)) (S.map Fin.castSuccEmb) d
        hij hS' hd) =
      ∑ t ∈ S, (#{s ∈ S | t ≤ s} : ℤ).negOnePow • lastCol hX hY f i (S.erase t) (d + 1) -
        if h : S.Nonempty then
          (#S : ℤ).negOnePow • lastCol hX hY f (S.min' h) (S.erase (S.min' h)) (d + 1)
        else 0 := by
  rw [boundary_def, map_sum]
  have hne_last : ∀ a ∈ S.map Fin.castSuccEmb, a ≠ Fin.last (n + 1) := fun a ha ↦ by
    obtain ⟨t, -, rfl⟩ := mem_map.1 ha
    exact Fin.castSucc_ne_last t
  rw [sum_bij (fun a _ ↦ a.1.castPred (hne_last a.1 a.2))
    (fun a _ ↦ by
      obtain ⟨_, ha⟩ := a
      obtain ⟨t, ht, rfl⟩ := mem_map.1 ha
      simpa using ht)
    (fun a _ b _ h ↦ Subtype.ext (by simpa using congrArg Fin.castSucc h))
    (fun t ht ↦ ⟨⟨t.castSucc, mem_map_of_mem _ ht⟩, mem_attach _ _, by simp⟩)
    (g := fun t ↦ (#{s ∈ S | t ≤ s} : ℤ).negOnePow • (lastCol hX hY f i (S.erase t) (d + 1) -
        if {s ∈ S | s < t} = ∅ then lastCol hX hY f t (S.erase t) (d + 1) else 0))
    (fun a _ ↦ by
      obtain ⟨_, ha⟩ := a
      obtain ⟨t, ht, rfl⟩ := mem_map.1 ha
      simp only [Fin.castSuccEmb_apply, Fin.castPred_castSucc]
      exact dgCast_boundary_term hX hY f hf hS hij hS' hd ht ha)]
  simp only [smul_sub, sum_sub_distrib]
  congr 1
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  rw [dite_eq_left hne, sum_eq_single_of_mem (S.min' hne) (min'_mem S hne) fun t ht htm ↦ by
    rw [ite_eq_right fun h ↦ htm (le_antisymm (not_lt.1 fun hlt ↦ (filter_eq_empty_iff.1 h)
      (min'_mem S hne) hlt) (min'_le S t ht)), smul_zero]]
  rw [ite_eq_left (filter_eq_empty_iff.2 fun s hs ↦ not_lt.2 (min'_le S s hs)),
    filter_true_of_mem fun s hs ↦ min'_le S s hs]

include hX in
private theorem obj_eq_of_ne_last {i : Fin (n + 2)} (hi : i ≠ Fin.last (n + 1)) : obj i = X := by
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hi
  exact hX i

include hX in
/-- The right-hand side of the dg nerve equation between two of the first `n + 1` vertices
vanishes for coherences of a constant simplex. -/
private theorem boundary_eq_zero_of_ne_last {f : Coherences R obj} (hf : IsConstInit f X)
    {i j : Fin (n + 2)} {S : Finset (Fin (n + 2))} {d : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hd : d + #S = 0) (hj : j ≠ Fin.last (n + 1)) : boundary R f i j S d hij hS hd = 0 := by
  rw [boundary_def]
  refine sum_eq_zero fun t _ ↦ ?_
  have htj : t.1 ≠ Fin.last (n + 1) :=
    ((mem_Ioo.1 (hS t.2)).2.trans_le (Fin.le_last j)).ne
  have hunion : S.erase t.1 = {s ∈ S | s < t.1} ∪ {s ∈ S | t.1 < s} := by
    ext s
    simp only [mem_erase, mem_union, mem_filter]
    constructor
    · rintro ⟨hst, hs⟩
      rcases lt_or_gt_of_ne hst with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
    · rintro (⟨hs, h⟩ | ⟨hs, h⟩)
      · exact ⟨h.ne, hs⟩
      · exact ⟨h.ne', hs⟩
  by_cases hS₁ : S.erase t.1 = ∅
  · -- `S = {t}`: the face term and the composite term are both identities.
    have hlt : {s ∈ S | s < t.1} = ∅ := (union_eq_empty.1 (hunion.symm.trans hS₁)).1
    have hgt : {s ∈ S | t.1 < s} = ∅ := (union_eq_empty.1 (hunion.symm.trans hS₁)).2
    have hS1 : #S = 1 := by
      have h₁ := card_erase_of_mem t.2
      have h₂ := card_pos.2 ⟨_, t.2⟩
      rw [hS₁, card_empty] at h₁
      omega
    have hcard : (#{s ∈ S | s < t.1} * #{s ∈ S | t.1 < s} : ℤ).negOnePow = 1 := by
      rw [hlt, card_empty, Nat.cast_zero, zero_mul, Int.negOnePow_zero]
    have ha := (heq_of_eq (Coherences.congr f hS₁ (hS := (erase_subset _ _).trans hS)
        (hd := add_one_add_card_erase_eq_zero t.2 hd))).trans
      (hf.2 i j (d + 1) hij (empty_subset _) (by rw [card_empty]; omega) hj)
    have hb := dgComp_heq_dgId (R := R) (a := f i t.1 {s ∈ S | s < t.1} _
        (mem_Ioo.1 (hS t.2)).1.le (filter_lt_subset_Ioo hS) (neg_add_cancel _))
      (b := f t.1 j {s ∈ S | t.1 < s} _ (mem_Ioo.1 (hS t.2)).2.le (filter_gt_subset_Ioo hS)
        (neg_add_cancel _)) (neg_card_filter_lt_add_neg_card_filter_gt t.2 hd)
      (obj_eq_of_ne_last hX ((hij.trans_lt (lt_of_le_of_ne (Fin.le_last j) hj)).ne))
      (obj_eq_of_ne_last hX htj) (obj_eq_of_ne_last hX hj) (by simp [hlt]) (by simp [hgt])
      ((heq_of_eq (Coherences.congr f hlt)).trans
        (hf.2 _ _ _ _ (empty_subset _) (by simp [hlt]) htj))
      ((heq_of_eq (Coherences.congr f hgt)).trans
        (hf.2 _ _ _ _ (empty_subset _) (by simp [hgt]) hj))
    rw [hcard, one_smul, eq_of_heq (ha.trans hb.symm), sub_self, smul_zero]
  · rw [hf.1 _ _ _ _ _ _ _ hj (nonempty_iff_ne_empty.2 hS₁)]
    rw [hunion] at hS₁
    obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.2 hS₁
    rcases mem_union.1 hs with hs | hs
    · rw [hf.1 _ _ _ _ _ _ _ htj ⟨s, hs⟩, zero_dgComp, smul_zero, sub_zero, smul_zero]
    · rw [hf.1 _ _ _ _ _ _ _ hj ⟨s, hs⟩, dgComp_zero, smul_zero, sub_zero, smul_zero]

/-- A nonempty set of vertices is a vertex `i` together with a set of vertices above `i`. -/
private theorem exists_insert_eq {J : Finset (Fin (n + 1))} (hJ : J.Nonempty) :
    ∃ i S, S ⊆ Ioi i ∧ insert i S = J :=
  ⟨J.min' hJ, J.erase (J.min' hJ), fun _ hs ↦ mem_Ioi.2 (lt_of_le_of_ne
    (min'_le _ _ (mem_of_mem_erase hs)) (ne_of_mem_erase hs).symm), insert_erase (min'_mem J hJ)⟩

/-- The values of the simplex chain map attached to last-column coherences: the value on a
nonempty `J` is the twisted coherence from the first vertex of `J` through the others to the last
vertex. -/
private noncomputable def chainVal (f : Coherences R obj) (J : Finset (Fin (n + 1))) (d : ℤ) :
    DGHom R d X Y :=
  if h : J.Nonempty then twist (#J - 1) • lastCol hX hY f (J.min' h) (J.erase (J.min' h)) d
  else 0

private theorem min'_insert_of_subset_Ioi {a : Fin (n + 1)} {T : Finset (Fin (n + 1))}
    (hT : T ⊆ Ioi a) : (insert a T).min' (insert_nonempty a T) = a :=
  le_antisymm (min'_le _ _ (mem_insert_self a T)) (le_min' _ _ _ fun y hy ↦ by
    rcases mem_insert.1 hy with rfl | hy
    · exact le_rfl
    · exact (mem_Ioi.1 (hT hy)).le)

private theorem chainVal_insert (f : Coherences R obj) {a : Fin (n + 1)}
    {T : Finset (Fin (n + 1))} (hT : T ⊆ Ioi a) (d : ℤ) :
    chainVal hX hY f (insert a T) d = twist #T • lastCol hX hY f a T d := by
  have ha : a ∉ T := notMem_of_subset_Ioi hT
  rw [chainVal, dite_eq_left (insert_nonempty a T)]
  simp only [min'_insert_of_subset_Ioi hT, erase_insert ha, card_insert_of_notMem ha,
    Nat.add_sub_cancel]

private theorem chainVal_empty (f : Coherences R obj) (d : ℤ) : chainVal hX hY f ∅ d = 0 :=
  dite_eq_right (by simp)

private theorem chainVal_eq_zero_of_ne (f : Coherences R obj) {J : Finset (Fin (n + 1))}
    {d : ℤ} (h : d + #J ≠ 1) : chainVal hX hY f J d = 0 := by
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · exact chainVal_empty hX hY f d
  · obtain ⟨i, S, hS, rfl⟩ := exists_insert_eq hJ
    have hi : i ∉ S := notMem_of_subset_Ioi hS
    rw [chainVal_insert hX hY f hS, lastCol_eq_zero hX hY f (by
      rw [card_insert_of_notMem hi] at h; push_cast at h; omega), smul_zero]

/-- The alternating sum over the faces of `insert i S` of the values `chainVal` is the twisted
transport of the right-hand side of the dg nerve equation for the last-column coherence through
`S`. -/
private theorem sum_faces_chainVal (f : Coherences R obj) (hf : IsConstInit f X)
    {i : Fin (n + 1)} {S : Finset (Fin (n + 1))} (hS : S ⊆ Ioi i) {d : ℤ}
    (hij : i.castSucc ≤ Fin.last (n + 1))
    (hS' : S.map Fin.castSuccEmb ⊆ Ioo i.castSucc (Fin.last (n + 1)))
    (hd : d + #(S.map Fin.castSuccEmb) = 0) :
    ∑ j ∈ insert i S, (#{s ∈ insert i S | s < j} : ℤ).negOnePow •
        chainVal hX hY f ((insert i S).erase j) (d + 1) =
      twist #S • dgCast (hX i) hY rfl
        (boundary R f i.castSucc (Fin.last (n + 1)) (S.map Fin.castSuccEmb) d hij hS' hd) := by
  rw [dgCast_boundary_last hX hY f hf hS hij hS' hd]
  exact sum_faces_insert (fun J ↦ chainVal hX hY f J (d + 1))
    (fun a T ↦ lastCol hX hY f a T (d + 1)) (chainVal_empty hX hY f _)
    (fun _ _ hT ↦ chainVal_insert hX hY f hT _) hS

/-- The simplex chain map attached to an `(n + 1)`-simplex of the differential graded nerve
whose restriction to the first `n + 1` vertices is the constant simplex at `X` and whose last
object is `Y`. -/
private noncomputable def toChainMap (σ : Simplex R C (n + 1))
    (hX : ∀ i : Fin (n + 1), σ.obj i.castSucc = X) (hY : σ.obj (Fin.last (n + 1)) = Y)
    (hσ : IsConstInit σ.coh X) : (dgHomComplex R X Y).SimplexChainMap n where
  val := chainVal hX hY σ.coh
  val_eq_zero_of_ne _ _ h := chainVal_eq_zero_of_ne hX hY σ.coh h
  val_empty := chainVal_empty hX hY σ.coh 1
  d_val J d := by
    -- The differential of the Hom complex is `dgDifferential`, an abbreviation.
    change dgDifferential R d (chainVal hX hY σ.coh J d) = _
    rcases J.eq_empty_or_nonempty with rfl | hJ
    · simp [chainVal_empty]
    obtain ⟨i, S, hS, rfl⟩ := exists_insert_eq hJ
    have hi : i ∉ S := notMem_of_subset_Ioi hS
    by_cases hd : d + #S = 0
    · have hd' : d + #(S.map Fin.castSuccEmb) = 0 := by rwa [card_map]
      rw [sum_faces_chainVal hX hY σ.coh hσ hS (Fin.castSucc_lt_last i).le
        (map_castSucc_subset_Ioo hS) hd', chainVal_insert hX hY σ.coh hS, dgDifferential_units_smul,
        ← lastCol_eq hX hY σ.coh hS rfl (Fin.castSucc_lt_last i).le (map_castSucc_subset_Ioo hS)
          hd' rfl, dgDifferential_dgCast, σ.dgDifferential_coh]
    · rw [chainVal_eq_zero_of_ne hX hY σ.coh (by rw [card_insert_of_notMem hi]; push_cast; omega),
        map_zero]
      refine (sum_eq_zero fun j hj ↦ ?_).symm
      rw [chainVal_eq_zero_of_ne hX hY σ.coh (by
        rw [card_erase_of_mem hj, card_insert_of_notMem hi]; push_cast; omega), smul_zero]

private theorem toChainMap_val (σ : Simplex R C (n + 1))
    (hX : ∀ i : Fin (n + 1), σ.obj i.castSucc = X) (hY : σ.obj (Fin.last (n + 1)) = Y)
    (hσ : IsConstInit σ.coh X) (J : Finset (Fin (n + 1))) (d : ℤ) :
    (toChainMap σ hX hY hσ).val J d = chainVal hX hY σ.coh J d :=
  (rfl)

/-! ### The simplex attached to a chain map -/

omit hX hY

variable (X Y) in
/-- The objects of the simplex attached to a chain map: `X` at the first `n + 1` vertices and `Y`
at the last one. -/
private def psiObj (i : Fin (n + 2)) : C := if i = Fin.last (n + 1) then Y else X

private theorem psiObj_of_ne {i : Fin (n + 2)} (hi : i ≠ Fin.last (n + 1)) : psiObj X Y i = X :=
  ite_eq_right hi

private theorem psiObj_last : psiObj X Y (Fin.last (n + 1)) = Y :=
  ite_eq_left rfl

private theorem psiObj_eq_of_eq_last {i : Fin (n + 2)} (hi : i = Fin.last (n + 1)) :
    psiObj X Y i = Y := by
  subst hi
  exact psiObj_last

private theorem psiObj_castSucc (i : Fin (n + 1)) : psiObj X Y i.castSucc = X :=
  psiObj_of_ne (Fin.castSucc_ne_last i)

private theorem eq_zero_of_subset_Ioo_last {S : Finset (Fin (n + 2))} {i : Fin (n + 2)}
    (hi : i = Fin.last (n + 1)) (hS : S ⊆ Ioo i (Fin.last (n + 1))) : S = ∅ := by
  rwa [hi, Ioo_self, subset_empty] at hS

/-- The coherences of the simplex attached to a chain map `g`: on the first `n + 1` vertices those
of the constant simplex at `X`, the identity of `Y` at the last vertex, and the twisted values of
`g` from a vertex `i` through `S` to the last vertex. -/
private noncomputable def psiCoh (g : (dgHomComplex R X Y).SimplexChainMap n) :
    Coherences R (psiObj (n := n) X Y) := fun i j S d _ hS hd ↦
  if hj : j = Fin.last (n + 1) then
    if hi : i = Fin.last (n + 1) then
      dgCast (psiObj_eq_of_eq_last hi).symm (psiObj_eq_of_eq_last hj).symm
        (by
          subst hj
          obtain rfl := eq_zero_of_subset_Ioo_last hi hS
          simpa using hd.symm) (dgId R Y)
    else
      twist #S • dgCast (psiObj_of_ne hi).symm (psiObj_eq_of_eq_last hj).symm rfl
        (g.val ((insert i S).preimage Fin.castSucc (Fin.castSucc_injective _).injOn) d)
  else
    if hS₀ : S = ∅ then
      dgCast (psiObj_of_ne fun hi ↦ hj (le_antisymm (Fin.le_last j) (hi ▸ ‹i ≤ j›))).symm
        (psiObj_of_ne hj).symm (by subst hS₀; simpa using hd.symm) (dgId R X)
    else 0

private theorem psiCoh_last_last_heq (g : (dgHomComplex R X Y).SimplexChainMap n)
    {S : Finset (Fin (n + 2))} {d : ℤ} (hij : Fin.last (n + 1) ≤ Fin.last (n + 1))
    (hS : S ⊆ Ioo (Fin.last (n + 1)) (Fin.last (n + 1))) (hd : d + #S = 0) :
    psiCoh g (Fin.last (n + 1)) (Fin.last (n + 1)) S d hij hS hd ≍ dgId R Y := by
  rw [psiCoh, dite_eq_left rfl, dite_eq_left rfl]
  exact dgCast_heq _ _ _ _

private theorem psiCoh_of_ne_last_empty_heq (g : (dgHomComplex R X Y).SimplexChainMap n)
    {i j : Fin (n + 2)} {d : ℤ} (hij : i ≤ j) (hS : ∅ ⊆ Ioo i j) (hd : d + #(∅ : Finset _) = 0)
    (hj : j ≠ Fin.last (n + 1)) : psiCoh g i j ∅ d hij hS hd ≍ dgId R X := by
  rw [psiCoh, dite_eq_right hj, dite_eq_left rfl]
  exact dgCast_heq _ _ _ _

private theorem psiCoh_of_ne_last_of_nonempty (g : (dgHomComplex R X Y).SimplexChainMap n)
    {i j : Fin (n + 2)} {S : Finset (Fin (n + 2))} {d : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hd : d + #S = 0) (hj : j ≠ Fin.last (n + 1)) (hne : S.Nonempty) :
    psiCoh g i j S d hij hS hd = 0 := by
  rw [psiCoh, dite_eq_right hj, dite_eq_right hne.ne_empty]

private theorem dgCast_psiCoh_castSucc_last (g : (dgHomComplex R X Y).SimplexChainMap n)
    {i : Fin (n + 1)} {S : Finset (Fin (n + 1))} {d : ℤ}
    (hij : i.castSucc ≤ Fin.last (n + 1))
    (hS : S.map Fin.castSuccEmb ⊆ Ioo i.castSucc (Fin.last (n + 1)))
    (hd : d + #(S.map Fin.castSuccEmb) = 0) :
    dgCast (psiObj_castSucc i) psiObj_last rfl
        (psiCoh g i.castSucc (Fin.last (n + 1)) (S.map Fin.castSuccEmb) d hij hS hd) =
      twist #S • g.val (insert i S) d := by
  rw [psiCoh, dite_eq_left rfl, dite_eq_right (Fin.castSucc_ne_last i), dgCast_units_smul,
    dgCast_dgCast, card_map]
  have hpre : (insert i.castSucc (S.map Fin.castSuccEmb)).preimage Fin.castSucc
      (Fin.castSucc_injective _).injOn = insert i S := by
    rw [← Fin.castSuccEmb_apply, ← map_insert]
    exact preimage_map Fin.castSuccEmb _
  rw [hpre]
  rfl

private theorem isConstInit_psiCoh (g : (dgHomComplex R X Y).SimplexChainMap n) :
    IsConstInit (psiCoh g) X :=
  ⟨fun _ _ _ _ hij hS hd hj hne ↦ psiCoh_of_ne_last_of_nonempty g hij hS hd hj hne,
    fun _ _ _ hij hS hd hj ↦ psiCoh_of_ne_last_empty_heq g hij hS hd hj⟩

private theorem chainVal_psiCoh (g : (dgHomComplex R X Y).SimplexChainMap n)
    (J : Finset (Fin (n + 1))) (d : ℤ) :
    chainVal psiObj_castSucc psiObj_last (psiCoh g) J d = g.val J d := by
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · rw [chainVal_empty, g.val_empty']
  obtain ⟨i, S, hS, rfl⟩ := exists_insert_eq hJ
  have hi : i ∉ S := notMem_of_subset_Ioi hS
  rw [chainVal_insert _ _ _ hS]
  by_cases hd : d + #S = 0
  · rw [← lastCol_eq psiObj_castSucc psiObj_last _ hS rfl (Fin.castSucc_lt_last i).le
      (map_castSucc_subset_Ioo hS) (by rwa [card_map]) rfl, dgCast_psiCoh_castSucc_last,
      smul_smul, twist_mul_self, one_smul]
  · rw [lastCol_eq_zero _ _ _ hd, smul_zero, g.val_eq_zero_of_ne _ _ (by
      rw [card_insert_of_notMem hi]; push_cast; omega)]

/-- The `(n + 1)`-simplex of the differential graded nerve attached to a simplex chain map. -/
private noncomputable def ofChainMap (g : (dgHomComplex R X Y).SimplexChainMap n) :
    Simplex R C (n + 1) where
  obj := psiObj X Y
  coh := psiCoh g
  coh_self i := by
    by_cases hi : i = Fin.last (n + 1)
    · subst hi
      exact eq_of_heq ((psiCoh_last_last_heq g _ _ _).trans (dgId_heq psiObj_last).symm)
    · exact eq_of_heq ((psiCoh_of_ne_last_empty_heq g _ _ _ hi).trans
        (dgId_heq (psiObj_of_ne hi)).symm)
  dgDifferential_coh i j S d hij hS hd := by
    by_cases hj : j = Fin.last (n + 1)
    · subst hj
      by_cases hi : i = Fin.last (n + 1)
      · -- The identity of `Y` at the last vertex is closed.
        subst hi
        obtain rfl := eq_zero_of_subset_Ioo_last rfl hS
        rw [boundary_empty]
        exact dgDifferential_eq_zero_of_heq_dgId psiObj_last psiObj_last (by simpa using hd)
          (psiCoh_last_last_heq g _ _ _)
      · -- A last-column coherence: the equation is that of the chain map `g`.
        obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hi
        obtain ⟨S, rfl⟩ := exists_map_castSucc_eq hS
        have hS₀ : S ⊆ Ioi i := subset_Ioi_of_map_castSucc hS
        apply dgCast_injective (psiObj_castSucc i) psiObj_last rfl
        have h := sum_faces_chainVal psiObj_castSucc psiObj_last (psiCoh g)
          (isConstInit_psiCoh g) hS₀ hij hS hd
        simp only [chainVal_psiCoh] at h
        rw [← dgDifferential_dgCast, dgCast_psiCoh_castSucc_last, dgDifferential_units_smul,
          g.d_val, h, smul_smul, twist_mul_self, one_smul]
    · -- Between the first `n + 1` vertices the coherences are those of a constant simplex.
      by_cases hS₀ : S = ∅
      · subst hS₀
        rw [boundary_empty]
        exact dgDifferential_eq_zero_of_heq_dgId
          (psiObj_of_ne ((hij.trans_lt (lt_of_le_of_ne (Fin.le_last j) hj)).ne))
          (psiObj_of_ne hj) (by simpa using hd) (psiCoh_of_ne_last_empty_heq g _ _ _ hj)
      · rw [psiCoh_of_ne_last_of_nonempty g hij hS hd hj (nonempty_iff_ne_empty.2 hS₀), map_zero,
          boundary_eq_zero_of_ne_last psiObj_castSucc (isConstInit_psiCoh g) hij hS hd hj]

/-- A simplex whose restriction to the first `n + 1` vertices is constant is recovered from its
simplex chain map. -/
private theorem ofChainMap_toChainMap (σ : Simplex R C (n + 1))
    (hX : ∀ i : Fin (n + 1), σ.obj i.castSucc = X) (hY : σ.obj (Fin.last (n + 1)) = Y)
    (hσ : IsConstInit σ.coh X) : ofChainMap (toChainMap σ hX hY hσ) = σ := by
  have hobj : ∀ i, psiObj X Y i = σ.obj i := fun i ↦ by
    by_cases hi : i = Fin.last (n + 1)
    · subst hi
      exact psiObj_last.trans hY.symm
    · exact (psiObj_of_ne hi).trans (obj_eq_of_ne_last hX hi).symm
  refine Simplex.ext (funext hobj) fun i j S d hij hS hd ↦ ?_
  by_cases hj : j = Fin.last (n + 1)
  · subst hj
    by_cases hi : i = Fin.last (n + 1)
    · subst hi
      obtain rfl := eq_zero_of_subset_Ioo_last rfl hS
      obtain rfl : d = 0 := by simpa using hd
      rw [σ.coh_self]
      exact (psiCoh_last_last_heq _ hij hS hd).trans (dgId_heq hY.symm)
    · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hi
      obtain ⟨S, rfl⟩ := exists_map_castSucc_eq hS
      have hS₀ : S ⊆ Ioi i := subset_Ioi_of_map_castSucc hS
      have h := dgCast_psiCoh_castSucc_last (toChainMap σ hX hY hσ) hij hS hd
      rw [toChainMap_val, chainVal_insert hX hY σ.coh hS₀, smul_smul, twist_mul_self, one_smul,
        ← lastCol_eq hX hY σ.coh hS₀ rfl hij hS hd rfl] at h
      exact (dgCast_heq _ _ _ _).symm.trans ((heq_of_eq h).trans (dgCast_heq _ _ _ _))
  · by_cases hS₀ : S = ∅
    · subst hS₀
      exact (psiCoh_of_ne_last_empty_heq _ hij hS hd hj).trans (hσ.2 _ _ _ _ _ _ hj).symm
    · rw [show (ofChainMap (toChainMap σ hX hY hσ)).coh i j S d hij hS hd = 0 from
        psiCoh_of_ne_last_of_nonempty _ hij hS hd hj (nonempty_iff_ne_empty.2 hS₀),
        hσ.1 _ _ _ _ _ _ _ hj (nonempty_iff_ne_empty.2 hS₀)]
      exact zero_heq_zero (hobj i) (hobj j)

/-- Pulling back along a simplicial operator of the right mapping space, which acts on the first
`n + 1` vertices by `α` and fixes the last one, pulls back the simplex chain map along `α`. -/
private theorem chainVal_map {m : ℕ} (σ : Simplex R C (n + 1))
    (hX : ∀ i : Fin (n + 1), σ.obj i.castSucc = X) (hY : σ.obj (Fin.last (n + 1)) = Y)
    (hσ : IsConstInit σ.coh X) (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (m + 2) →o Fin (n + 2))
    (hβ : ∀ i, β i.castSucc = (α i).castSucc) (hβl : β (Fin.last (m + 1)) = Fin.last (n + 1))
    (hX' : ∀ i : Fin (m + 1), (σ.map β).obj i.castSucc = X)
    (hY' : (σ.map β).obj (Fin.last (m + 1)) = Y) (J : Finset (Fin (m + 1))) (d : ℤ) :
    chainVal hX' hY' (σ.map β).coh J d = ((toChainMap σ hX hY hσ).map α).val J d := by
  rw [CochainComplex.SimplexChainMap.map_val, toChainMap_val]
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · rw [chainVal_empty, image_empty, chainVal_empty, ite_self]
  obtain ⟨i, S, hS, rfl⟩ := exists_insert_eq hJ
  have hi : i ∉ S := notMem_of_subset_Ioi hS
  rw [chainVal_insert hX' hY' _ hS]
  by_cases hd : d + #S = 0
  swap
  · rw [lastCol_eq_zero _ _ _ hd, smul_zero]
    split_ifs with h
    · rw [chainVal_eq_zero_of_ne hX hY _ (by rw [h, card_insert_of_notMem hi]; push_cast; omega)]
    · rfl
  have hd' : d + #(S.map Fin.castSuccEmb) = 0 := by rwa [card_map]
  rw [← lastCol_eq hX' hY' _ hS rfl (Fin.castSucc_lt_last i).le (map_castSucc_subset_Ioo hS) hd'
    rfl, Simplex.map_coh]
  have himage : (S.map Fin.castSuccEmb).image β = (S.image α).map Fin.castSuccEmb := by
    ext s
    simp [hβ]
  -- Both sides are nonzero exactly when `α` is injective on `insert i S`.
  have hiff : (#((S.map Fin.castSuccEmb).image β) = #(S.map Fin.castSuccEmb) ∧
      (S.map Fin.castSuccEmb).image β ⊆ Ioo (β i.castSucc) (β (Fin.last (m + 1)))) ↔
      #((insert i S).image α) = #(insert i S) := by
    rw [himage, card_map, card_map, hβ, hβl, card_image_iff, card_image_iff, coe_insert,
      Set.injOn_insert (by simpa using hi)]
    refine and_congr Iff.rfl ⟨fun h ⟨s, hs, hs'⟩ ↦ ?_, fun h t ht ↦ ?_⟩
    · have := mem_Ioo.1 (h (mem_map_of_mem _ (mem_image_of_mem α hs)))
      simp only [Fin.castSuccEmb_apply, Fin.castSucc_lt_castSucc_iff] at this
      exact this.1.ne' hs'
    · obtain ⟨u, hu, rfl⟩ := mem_map.1 ht
      obtain ⟨s, hs, rfl⟩ := mem_image.1 hu
      refine mem_Ioo.2 ⟨Fin.castSucc_lt_castSucc_iff.2 (lt_of_le_of_ne
        (α.monotone (mem_Ioi.1 (hS hs)).le) fun h' ↦ h ⟨s, hs, h'.symm⟩), Fin.castSucc_lt_last _⟩
  by_cases hinj : #((insert i S).image α) = #(insert i S)
  · have hcard : #(S.image α) = #S := card_image_iff.2
      ((card_image_iff.1 hinj).mono (coe_subset.2 (subset_insert i S)))
    have hSα : S.image α ⊆ Ioi (α i) := fun s hs ↦ by
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hs
      have := hiff.2 hinj |>.2 (mem_image_of_mem β (mem_map_of_mem _ ht))
      simpa [hβ, hβl, Fin.castSucc_lt_castSucc_iff] using (mem_Ioo.1 this).1
    rw [ite_eq_left hinj, image_insert, chainVal_insert hX hY _ hSα, hcard,
      ← lastCol_eq hX hY _ hSα rfl (Fin.castSucc_lt_last _).le (map_castSucc_subset_Ioo hSα)
        (by rwa [card_map, hcard]) rfl, Simplex.mapCoh_eq_coh _ _ (hiff.2 hinj)]
    congr 1
    exact eq_of_heq ((dgCast_heq _ _ _ _).trans ((σ.coh_heq (hβ i) hβl himage).trans
      (dgCast_heq _ _ _ _).symm))
  · rw [Simplex.mapCoh_eq_zero _ _ (fun h ↦ hinj (hiff.1 h)), ite_eq_right hinj]
    exact (congrArg _ (map_zero _)).trans (smul_zero _)

/-! ### Simplices of the right mapping space -/

private theorem castDeg_heq {X Y : C} {p p' : ℤ} (hp : p = p') (f : DGHom R p X Y) :
    castDeg R hp f ≍ f := by
  subst hp
  simp

private theorem eq_zero_of_heq_zero {A B X : C} {d : ℤ} {a : DGHom R d A B} (hA : A = X)
    (hB : B = X) (h : a ≍ (0 : DGHom R d X X)) : a = 0 := by
  subst hA hB
  exact eq_of_heq h

/-- The coherences of a constant simplex without interior vertices are identities. -/
private theorem coh_map_vertex_empty_heq {m : ℕ} (X : C) (α : Fin (m + 1) →o Fin 1)
    {i j : Fin (m + 1)} {d : ℤ} (hij : i ≤ j) (hS : ∅ ⊆ Ioo i j) (hd : d + #(∅ : Finset _) = 0) :
    ((Simplex.vertex X : Simplex R C 0).map α).coh i j ∅ d hij hS hd ≍ dgId R X := by
  rw [Simplex.map_coh, Simplex.mapCoh_eq_coh _ _ (by simp)]
  exact castDeg_heq _ _

/-- The coherences of a constant simplex with interior vertices vanish. -/
private theorem coh_map_vertex_of_nonempty {m : ℕ} (X : C) (α : Fin (m + 1) →o Fin 1)
    {i j : Fin (m + 1)} {S : Finset (Fin (m + 1))} {d : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hd : d + #S = 0) (hne : S.Nonempty) :
    ((Simplex.vertex X : Simplex R C 0).map α).coh i j S d hij hS hd = 0 := by
  rw [Simplex.map_coh]
  refine Simplex.mapCoh_eq_zero _ _ fun ⟨_, h⟩ ↦ ?_
  obtain ⟨s, hs⟩ := hne
  have := h (mem_image_of_mem α hs)
  simp [Subsingleton.elim (α i) (α j)] at this

private theorem δ_last_apply (j : Fin (n + 1)) :
    (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom j = j.castSucc :=
  Fin.succAbove_last_apply j

/-- A coherence of the face of a simplex opposite to its last vertex is a coherence of the
simplex. -/
private theorem coh_δ_last_heq (σ : Simplex R C (n + 1)) {i j : Fin (n + 1)}
    {S : Finset (Fin (n + 1))} {d : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j) (hd : d + #S = 0)
    (hij' : i.castSucc ≤ j.castSucc) (hS' : S.map Fin.castSuccEmb ⊆ Ioo i.castSucc j.castSucc)
    (hd' : d + #(S.map Fin.castSuccEmb) = 0) :
    (σ.map (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom).coh i j S d hij hS hd ≍
      σ.coh i.castSucc j.castSucc (S.map Fin.castSuccEmb) d hij' hS' hd' := by
  have himage : S.image (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom =
      S.map Fin.castSuccEmb := by
    ext s
    simp [δ_last_apply]
  rw [Simplex.map_coh_of_strictMono _ _ (fun a b h ↦ Fin.strictMono_succAbove _ h)
    hij hS hd (by rw [himage, δ_last_apply, δ_last_apply]; exact hS')]
  exact σ.coh_heq (δ_last_apply i) (δ_last_apply j) himage

end DGNerve

open DGNerve

namespace dgNerve

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-- The simplices of the right mapping space `Hom^R_{N_dg(C)}(X, Y)`: an `(n + 1)`-simplex of the
differential graded nerve is an `n`-simplex of `Hom^R_{N_dg(C)}(X, Y)` exactly when its first
`n + 1` objects are `X`, its last object is `Y`, and its coherences between the first `n + 1`
vertices are identities without interior vertices and zero otherwise. -/
theorem mem_rightMappingSpace_iff {X Y : C} {n : ℕ} (σ : Simplex R C (n + 1)) :
    σ ∈ ((dgNerve R C).rightMappingSpace ((dgNerveEquiv R C).symm X)
        ((dgNerveEquiv R C).symm Y)).obj (op ⦋n⦌) ↔
      (∀ i : Fin (n + 1), σ.obj i.castSucc = X) ∧ σ.obj (Fin.last (n + 1)) = Y ∧
        (∀ i j S d hij hS hd, j ≠ Fin.last (n + 1) → S.Nonempty →
          σ.coh i j S d hij hS hd = 0) ∧
        ∀ i j d hij hS hd, j ≠ Fin.last (n + 1) → σ.coh i j ∅ d hij hS hd ≍ dgId R X := by
  -- The simplicial operators of the differential graded nerve act by `Simplex.map`
  -- (`dgNerve_δ` and `dgNerve_map_apply`, which hold by `rfl`); we state the two conditions of
  -- `SSet.mem_rightMappingSpace_iff` on `σ` as a simplex rather than an element of `dgNerve R C`.
  simp only [dgNerveEquiv_symm_apply]
  refine (SSet.mem_rightMappingSpace_iff (X := dgNerve R C) σ).trans (Iff.trans (b :=
    σ.map (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom =
        (Simplex.vertex X).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom ∧
      σ.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))).toOrderHom =
        Simplex.vertex Y) Iff.rfl ?_)
  constructor
  · rintro ⟨h₁, h₂⟩
    have hX : ∀ i : Fin (n + 1), σ.obj i.castSucc = X := fun i ↦ by
      simpa [δ_last_apply] using congrArg (fun s : Simplex R C n ↦ s.obj i) h₁
    -- A coherence between the first `n + 1` vertices is one of the constant last face.
    have key : ∀ (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (d : ℤ) (hij₀ : i ≤ j)
        (hS₀ : S ⊆ Ioo i j) (hd₀ : d + #S = 0) hij hS hd,
        σ.coh i.castSucc j.castSucc (S.map Fin.castSuccEmb) d hij hS hd ≍
          ((Simplex.vertex X : Simplex R C 0).map
            (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom).coh i j S d hij₀ hS₀ hd₀ :=
      fun i j S d hij₀ hS₀ hd₀ hij hS hd ↦ (coh_δ_last_heq σ hij₀ hS₀ hd₀ hij hS hd).symm.trans
        (congr_arg_heq (fun s : Simplex R C n ↦ s.coh i j S d hij₀ hS₀ hd₀) h₁)
    refine ⟨hX, by simpa using congrArg (fun s : Simplex R C 0 ↦ s.obj 0) h₂, ?_, ?_⟩
    · intro i j S d hij hS hd hj hne
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt (lt_of_le_of_lt hij
        (Fin.castSucc_lt_last j)))
      obtain ⟨S, rfl⟩ := exists_map_castSucc_eq hS
      exact eq_zero_of_heq_zero (hX i) (hX j) ((key i j S d (Fin.castSucc_le_castSucc_iff.1 hij)
        (subset_Ioo_of_map_castSucc hS) (by rwa [card_map] at hd) hij hS hd).trans
        (heq_of_eq (coh_map_vertex_of_nonempty X _ _ _ _ (by simpa using hne))))
    · intro i j d hij hS hd hj
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt (lt_of_le_of_lt hij
        (Fin.castSucc_lt_last j)))
      exact (σ.coh_heq rfl rfl (map_empty _).symm).trans ((key i j ∅ d
        (Fin.castSucc_le_castSucc_iff.1 hij) (empty_subset _) (by simpa using hd) hij (by simp)
        (by simpa using hd)).trans (coh_map_vertex_empty_heq X _ _ _ _))
  · rintro ⟨hX, hY, h₀, h₁⟩
    refine ⟨Simplex.ext (funext fun i ↦ by simp [δ_last_apply, hX]) fun i j S d hij hS hd ↦
      (coh_δ_last_heq σ hij hS hd (Fin.castSucc_le_castSucc_iff.2 hij)
        (fun s hs ↦ by
          obtain ⟨t, ht, rfl⟩ := mem_map.1 hs
          simpa [Fin.castSucc_lt_castSucc_iff] using hS ht)
        (by rwa [card_map])).trans ?_, Simplex.ext_zero (by simpa using hY)⟩
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact (σ.coh_heq rfl rfl (map_empty _)).trans ((h₁ _ _ _ (Fin.castSucc_le_castSucc_iff.2 hij)
        (by simp) (by simpa using hd)
        (Fin.castSucc_ne_last j)).trans (coh_map_vertex_empty_heq X _ _ _ _).symm)
    · rw [h₀ _ _ _ _ _ _ _ (Fin.castSucc_ne_last j) (hne.map),
        coh_map_vertex_of_nonempty X _ _ _ _ hne]
      exact zero_heq_zero (hX i) (hX j)

/-- The `n`-simplices of the right mapping space `Hom^R_{N_dg(C)}(X, Y)` are the chain maps from
the normalized chains of `Δ[n]` to the good truncation `τ_{≥ 0} Hom_C(X, Y)`. An `n`-simplex goes to
its coherences from the first `n + 1` vertices to the last one, multiplied by the signs
`(-1) ^ (r choose 2)` (`TauCeti.dgNerve.rightMappingSpaceEquiv_apply_val_insert_heq`). -/
noncomputable def rightMappingSpaceEquiv (X Y : C) (n : ℕ) :
    ((dgNerve R C).rightMappingSpace ((dgNerveEquiv R C).symm X)
      ((dgNerveEquiv R C).symm Y) : SSet) _⦋n⦌ ≃ (dgHomComplex R X Y).SimplexChainMap n where
  toFun s :=
    have h := (mem_rightMappingSpace_iff (s.1 : Simplex R C (n + 1))).1 s.2
    toChainMap _ h.1 h.2.1 ⟨h.2.2.1, h.2.2.2⟩
  invFun g := ⟨ofChainMap g, (mem_rightMappingSpace_iff _).2
    ⟨psiObj_castSucc, psiObj_last, (isConstInit_psiCoh g).1, (isConstInit_psiCoh g).2⟩⟩
  left_inv _ := Subtype.ext (ofChainMap_toChainMap _ _ _ _)
  right_inv g := CochainComplex.SimplexChainMap.ext (funext₂ (chainVal_psiCoh g))

/-- The value of the chain map attached to an `n`-simplex `σ` of `Hom^R_{N_dg(C)}(X, Y)` on
`insert i S`, for a set `S` of vertices above `i`, is the coherence of `σ` from `i` through `S` to
the last vertex, multiplied by `(-1) ^ (#S choose 2)`. -/
theorem rightMappingSpaceEquiv_apply_val_insert_heq {X Y : C} {n : ℕ} (σ : Simplex R C (n + 1))
    (hσ : σ ∈ ((dgNerve R C).rightMappingSpace ((dgNerveEquiv R C).symm X)
      ((dgNerveEquiv R C).symm Y)).obj (op ⦋n⦌)) {i : Fin (n + 1)} {S : Finset (Fin (n + 1))}
    (hS : S ⊆ Ioi i) {d : ℤ} (hd : d + #S = 0) :
    (((#S).choose 2 : ℕ) : ℤ).negOnePow •
        (rightMappingSpaceEquiv X Y n ⟨σ, hσ⟩).val (insert i S) d ≍
      σ.coh i.castSucc (Fin.last (n + 1)) (S.map Fin.castSuccEmb) d (Fin.castSucc_lt_last i).le
        (by exact map_castSucc_subset_Ioo hS) (by rwa [card_map]) := by
  have h := (mem_rightMappingSpace_iff σ).1 hσ
  -- The chain map attached to `σ` is `toChainMap`, whose values are `chainVal` by definition.
  rw [show (rightMappingSpaceEquiv X Y n ⟨σ, hσ⟩).val = chainVal h.1 h.2.1 σ.coh from rfl,
    chainVal_insert _ _ _ hS, smul_smul, twist_mul_self, one_smul, ← lastCol_eq h.1 h.2.1 _ hS
    rfl (Fin.castSucc_lt_last i).le (map_castSucc_subset_Ioo hS) (by rwa [card_map]) rfl]
  exact dgCast_heq _ _ _ _

/-- **The right mapping spaces of the differential graded nerve.** For objects `X` and `Y` of a
differential graded category, `Hom^R_{N_dg(C)}(X, Y)` is isomorphic to the simplicial set of chain
maps from the normalized chains of the standard simplices to the good truncation
`τ_{≥ 0} Hom_C(X, Y)`. -/
noncomputable def rightMappingSpaceIso (X Y : C) :
    ((dgNerve R C).rightMappingSpace ((dgNerveEquiv R C).symm X)
      ((dgNerveEquiv R C).symm Y) : SSet) ≅
      SSet.uliftFunctor.{u, v}.obj (dgHomComplex R X Y).simplexChainMaps :=
  NatIso.ofComponents
    (fun Δ ↦ ((rightMappingSpaceEquiv X Y Δ.unop.len).trans Equiv.ulift.symm).toIso)
    fun {Δ Δ'} f ↦ by
      ext s : 3
      refine ULift.ext (CochainComplex.SimplexChainMap.ext (funext₂ fun J d ↦ ?_))
      have h := (mem_rightMappingSpace_iff (s.1 : Simplex R C (Δ.unop.len + 1))).1 s.2
      exact chainVal_map _ h.1 h.2.1 ⟨h.2.2.1, h.2.2.2⟩ f.unop.toOrderHom
        (SimplexCategory.joinVertex.map f.unop).toOrderHom
        (SimplexCategory.joinVertex_map_castSucc f.unop)
        (SimplexCategory.joinVertex_map_last f.unop) _ _ J d

end dgNerve

end TauCeti
