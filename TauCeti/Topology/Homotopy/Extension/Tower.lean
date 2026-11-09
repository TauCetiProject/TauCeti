/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Coherent
public import TauCeti.Topology.Homeomorph.SubtypeSubtype
public import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel

/-!
# Homotopy equivalences of towers of cofibrations

Let `X` be the union of an increasing sequence of subsets `A 0 ⊆ A 1 ⊆ ⋯`, each of which has the
homotopy extension property in the next, and suppose that `X` carries the topology coherent with
the `A n`; let `Y` be such a union of `B 0 ⊆ B 1 ⊆ ⋯`. The union of the skeleta of a CW complex
is of this kind, and so is a manifold exhausted by the regular sublevels of a proper function,
whose inclusions are closed cofibrations thanks to collars of the regular levels.

Let `f : X → Y` restrict, for every `n`, to a homotopy equivalence `A n ≃ₕ B n`. Then `f` is a
homotopy equivalence, with a homotopy inverse mapping each `B n` into `A n`
(`TauCeti.exists_homotopyEquiv_of_isCoherentWith`). The maps `f` and `A n → B n` commute
strictly with the inclusions; no homotopy inverse of the stages is part of the data.

The proof builds strictly compatible inverses. A homotopy inverse `g n : B n → A n` of the stage
`n`, together with a homotopy `g n ∘ f ≃ id`, extends to the stage `n + 1` without changing either
on the stage `n` (`TauCeti.HasHomotopyExtensionProperty.exists_inverse_extending_homotopy`).
Inductively this gives maps and homotopies which agree on overlaps, and they glue
(`ContinuousMap.liftCoherent`) to a map `g : Y → X` with a homotopy `g ∘ f ≃ id` which preserve
the stages (`TauCeti.exists_leftInverse_homotopy_of_isCoherentWith`). The homotopy is glued over
the products `I × A n`, which carry the topology of `I × X` as the unit interval is locally
compact (`Topology.IsCoherentWith.univ_prod`). The restrictions of `g` are homotopy equivalences
`B n ≃ₕ A n`, so the same construction gives a left homotopy inverse of `g`. Since `f` is a right
homotopy inverse of `g`, the map `g` is a two-sided homotopy inverse of `f`.

## Main results

* `TauCeti.exists_leftInverse_homotopy_of_isCoherentWith`: a left homotopy inverse `g` of `f`,
  together with a homotopy `g ∘ f ≃ id`, both preserving the stages.
* `TauCeti.exists_homotopyEquiv_of_isCoherentWith`: `f` is a homotopy equivalence, with a homotopy
  inverse preserving the stages.

## References

* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Chapter 5, for
  cofibrations and homotopy equivalences of pairs.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.19 and its proof, for the extension of inverses over a cofibration.
-/

public section

open Set Topology ContinuousMap unitInterval

namespace TauCeti

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- One stage of the induction: a homotopy inverse `g : T → S` of a homotopy equivalence
`e : S ≃ₕ T`, with a homotopy `g ∘ e ≃ id`, extends to a homotopy inverse of a homotopy
equivalence `e' : S' ≃ₕ T'` of larger subsets agreeing with `e` on `S`, with a homotopy which is
the given one on `S`. -/
private theorem exists_stage_extension {S S' : Set X} {T T' : Set Y} (hS : S ⊆ S') (hT : T ⊆ T')
    (hSH : HasHomotopyExtensionProperty ((↑) ⁻¹' S : Set S'))
    (hTH : HasHomotopyExtensionProperty ((↑) ⁻¹' T : Set T')) {f : X → Y}
    (e : S ≃ₕ T) (he : ∀ a : S, (e a : Y) = f a) (e' : S' ≃ₕ T')
    (he' : ∀ a : S', (e' a : Y) = f a) (g : C(T, S))
    (H : (g.comp e.toFun).Homotopy (ContinuousMap.id S)) :
    ∃ (g' : C(T', S')) (H' : (g'.comp e'.toFun).Homotopy (ContinuousMap.id S')),
      (∀ b : T, (g' (Set.inclusion hT b) : X) = g b) ∧
        ∀ (t : I) (a : S), (H' (t, Set.inclusion hS a) : X) = H (t, a) := by
  -- Read the stages `S` and `T` as subsets of `S'` and `T'`.
  let iS : ((↑) ⁻¹' S : Set S') ≃ₜ S := Homeomorph.subtypeSubtypeEquivSubtype fun h ↦ hS h
  let iT : ((↑) ⁻¹' T : Set T') ≃ₜ T := Homeomorph.subtypeSubtypeEquivSubtype fun h ↦ hT h
  -- Transport `e`, `g` and `H` to these subsets. The homeomorphisms `iS` and `iT` and their
  -- inverses only change membership proofs, so the transported data agree with the original
  -- data definitionally on points.
  let e₀ : ((↑) ⁻¹' S : Set S') ≃ₕ ((↑) ⁻¹' T : Set T') :=
    iS.toHomotopyEquiv.trans (e.trans iT.symm.toHomotopyEquiv)
  have he₀ (a : ((↑) ⁻¹' S : Set S')) : (e₀ a : T') = e' a :=
    Subtype.ext <| (he (iS a)).trans (he' a).symm
  let g₀ : C(((↑) ⁻¹' T : Set T'), ((↑) ⁻¹' S : Set S')) :=
    (iS.symm : C(S, _)).comp (g.comp (iT : C(_, T)))
  let H₀ : (g₀.comp e₀.toFun).Homotopy (ContinuousMap.id _) :=
    ((Homotopy.refl (iS.symm : C(S, _))).comp (H.compContinuousMap (iS : C(_, S)))).cast rfl rfl
  obtain ⟨g', H', hg', hH', -⟩ := hSH.exists_inverse_extending_homotopy hTH e' e₀ he₀ g₀ H₀
  exact ⟨g', H', fun b => congrArg Subtype.val (hg' (iT.symm b)),
    fun t a => congrArg Subtype.val (hH' t (iS.symm a))⟩

variable {A : ℕ → Set X} {B : ℕ → Set Y}

/-- **Left homotopy inverses of maps of towers.** Let `X` be the union of an increasing sequence
`A n`, each with the homotopy extension property in the next, carrying the topology coherent with
it, and likewise `Y` with `B n`. If `f : X → Y` restricts to homotopy equivalences
`e n : A n ≃ₕ B n`, then there are a map `g : Y → X` carrying each `B n` into `A n` and a
homotopy `g ∘ f ≃ id` keeping each `A n` in itself. -/
theorem exists_leftInverse_homotopy_of_isCoherentWith (hA : Monotone A) (hB : Monotone B)
    (hAX : ⋃ n, A n = univ) (hBY : ⋃ n, B n = univ) (hAc : IsCoherentWith (range A))
    (hBc : IsCoherentWith (range B))
    (hAH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' A n : Set (A (n + 1))))
    (hBH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' B n : Set (B (n + 1))))
    (f : C(X, Y)) (e : ∀ n, A n ≃ₕ B n) (he : ∀ n (a : A n), (e n a : Y) = f a) :
    ∃ (g : C(Y, X)) (H : (g.comp f).Homotopy (ContinuousMap.id X)),
      (∀ n, MapsTo g (B n) (A n)) ∧ ∀ n (t : I), ∀ x ∈ A n, H (t, x) ∈ A n := by
  choose G K hG hK using fun n ↦
    exists_stage_extension (hA n.le_succ) (hB n.le_succ) (hAH n) (hBH n) (e n) (he n) (e (n + 1))
      (he (n + 1))
  -- The inverses and homotopies of all stages, built inductively.
  let P (n : ℕ) : Type u :=
    Σ g : C(B n, A n), (g.comp (e n).toFun).Homotopy (ContinuousMap.id (A n))
  let s (n : ℕ) : P n := Nat.rec (motive := P) ⟨(e 0).invFun, (e 0).left_inv.some⟩
    (fun n p ↦ ⟨G n p.1 p.2, K n p.1 p.2⟩) n
  -- They agree on the earlier stages. Inclusions of stages compose definitionally, as
  -- `Set.inclusion` only changes the membership proof.
  have hs_g {m n : ℕ} (hmn : m ≤ n) (b : B m) :
      ((s n).1 (Set.inclusion (hB hmn) b) : X) = (s m).1 b := by
    induction hmn with
    | refl => rfl
    | step _ ih => exact (hG _ (s _).1 (s _).2 _).trans ih
  have hs_H {m n : ℕ} (hmn : m ≤ n) (t : I) (a : A m) :
      ((s n).2 (t, Set.inclusion (hA hmn) a) : X) = (s m).2 (t, a) := by
    induction hmn with
    | refl => rfl
    | step _ ih => exact (hK _ (s _).1 (s _).2 t _).trans ih
  -- Glue the inverses over the cover of `Y` by the `B n`.
  let g : C(Y, X) := liftCoherent B (fun n ↦ (subtypeVal (A n)).comp (s n).1)
    (fun i j y hi hj ↦ (hs_g (le_max_left i j) ⟨y, hi⟩).symm.trans
      (hs_g (le_max_right i j) ⟨y, hj⟩)) hBc hBY
  have hg (n : ℕ) (b : B n) : g b = (s n).1 b := liftCoherent_coe b
  -- Glue the homotopies over the cover of `I × X` by the `I × A n`.
  have hIX : ⋃ n, (univ : Set I) ×ˢ A n = univ := by simp [← prod_iUnion, hAX]
  let Hs (n : ℕ) : C((univ : Set I) ×ˢ A n, X) :=
    (subtypeVal (A n)).comp <| (s n).2.toContinuousMap.comp
      ⟨fun p ↦ (p.1.1, ⟨p.1.2, p.2.2⟩), by fun_prop⟩
  let HX : C(I × X, X) := liftCoherent (fun n ↦ (univ : Set I) ×ˢ A n) Hs
    (fun i j p hi hj ↦ (hs_H (le_max_left i j) p.1 ⟨p.2, hi.2⟩).symm.trans
      (hs_H (le_max_right i j) p.1 ⟨p.2, hj.2⟩)) (hAc.univ_prod hAX) hIX
  have hHX (n : ℕ) (t : I) (a : A n) : HX (t, a) = (s n).2 (t, a) :=
    liftCoherent_coe (S := fun n ↦ (univ : Set I) ×ˢ A n) ⟨(t, a), mem_univ t, a.2⟩
  have hmem (x : X) : ∃ n, x ∈ A n := mem_iUnion.1 (hAX ▸ mem_univ x)
  refine ⟨g, ⟨HX, fun x ↦ ?_, fun x ↦ ?_⟩, fun n y hy ↦ ?_, fun n t x hx ↦ ?_⟩
  · obtain ⟨n, hx⟩ := hmem x
    simp [hHX n 0 ⟨x, hx⟩, ← he n ⟨x, hx⟩, hg n]
  · obtain ⟨n, hx⟩ := hmem x
    simp [hHX n 1 ⟨x, hx⟩]
  · simp [hg n ⟨y, hy⟩]
  · -- The glued homotopy is `HX` as a function.
    have hH := ((s n).2 (t, ⟨x, hx⟩)).2
    rw [← hHX n t ⟨x, hx⟩] at hH
    exact hH

/-- **Maps of towers of cofibrations which are homotopy equivalences on every stage are homotopy
equivalences.** Let `X` be the union of an increasing sequence `A n`, each with the homotopy
extension property in the next, carrying the topology coherent with it, and likewise `Y` with
`B n`. If `f : X → Y` restricts to homotopy equivalences `e n : A n ≃ₕ B n`, then `f` is a
homotopy equivalence, with a homotopy inverse carrying each `B n` into `A n`. -/
theorem exists_homotopyEquiv_of_isCoherentWith (hA : Monotone A) (hB : Monotone B)
    (hAX : ⋃ n, A n = univ) (hBY : ⋃ n, B n = univ) (hAc : IsCoherentWith (range A))
    (hBc : IsCoherentWith (range B))
    (hAH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' A n : Set (A (n + 1))))
    (hBH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' B n : Set (B (n + 1))))
    (f : C(X, Y)) (e : ∀ n, A n ≃ₕ B n) (he : ∀ n (a : A n), (e n a : Y) = f a) :
    ∃ h : X ≃ₕ Y, ⇑h = f ∧ ∀ n, MapsTo h.symm (B n) (A n) := by
  obtain ⟨g, H, hgB, hHA⟩ :=
    exists_leftInverse_homotopy_of_isCoherentWith hA hB hAX hBY hAc hBc hAH hBH f e he
  -- On each stage, `g` is a left homotopy inverse of `e n`, hence a homotopy equivalence.
  let e' (n : ℕ) : B n ≃ₕ A n :=
    have Hn : (ContinuousMap.comp ⟨fun b ↦ ⟨g b, hgB n b.2⟩, by fun_prop⟩ (e n).toFun).Homotopy
        (ContinuousMap.id (A n)) :=
      { toFun p := ⟨H (p.1, p.2), hHA n p.1 p.2 p.2.2⟩
        map_zero_left a := Subtype.ext <| by simp [he]
        map_one_left a := Subtype.ext <| by simp }
    { toFun := ⟨fun b ↦ ⟨g b, hgB n b.2⟩, by fun_prop⟩
      invFun := (e n).toFun
      left_inv := (e n).toFun_comp_homotopic_id_of_comp_toFun_homotopic_id ⟨Hn⟩
      right_inv := ⟨Hn⟩ }
  -- The same construction gives a left homotopy inverse `k` of `g`.
  obtain ⟨k, K, -, -⟩ :=
    exists_leftInverse_homotopy_of_isCoherentWith hB hA hBY hAX hBc hAc hBH hAH g e' fun _ _ ↦ rfl
  -- Since `f` is a right homotopy inverse of `g`, so is `k`, and `f ∘ g ≃ k ∘ g ≃ id`.
  have hkf : k.Homotopic f := Homotopic.homotopic_of_comp_homotopic_id ⟨K⟩ ⟨H⟩
  exact ⟨⟨f, g, ⟨H⟩, (hkf.symm.comp (.refl g)).trans ⟨K⟩⟩, rfl, hgB⟩

end TauCeti
