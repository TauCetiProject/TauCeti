/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Iterated
import TauCeti.GroupTheory.Coprod.Reduced

/-!
# Free products with free and free abelian groups embed in extensions of centralizers

Let `u` be an element of a group `G` whose centralizer `C = C_G(u)` is malnormal, as in every CSA
group, let `g ∉ C`, and let `tᵢ` be a new letter of the extension `G(u, ℤⁿ) = G ∗_C (C × ℤⁿ)`.
For an embedding `f : K →* G`, the following homomorphisms out of free products are injective and
are `f` on `K`:

* `K ∗ A →* G(u, ℤⁿ)` for a subgroup `A` of `ℤⁿ`, sending `a ∈ A` to `(tᵢ g) a (tᵢ g)⁻¹`;
* `K ∗ F(X) →* G(u, ℤⁿ)`, sending the generator `x` to `(tᵢ g tᵢ^{m x} g) tᵢ (tᵢ g tᵢ^{m x} g)⁻¹`,
  for an injective `m : X → ℤ` with nonzero values.

For `K = G` the second one embeds the free `G`-group `G[X] = G ∗ F(X)` on a countable set `X`
over `G` in the single extension `G(u, ℤ)`. Over a nonabelian fully residually free group `H`, an
element `u` that is not a proper power and an element `g ∉ C_H(u)` exist by root reduction, so
`H[X]` and `H ∗ ℤⁿ` embed over `H` in one admissible extension of a centralizer of `H`. These are
the free and the free abelian levels of a normalized tower over `H`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.coprodPiLift_injective`: `K ∗ A` embeds in `G(u, ℤⁿ)`.
* `TauCeti.LimitGroup.CentralizerExt.coprodFreeGroupLift_injective`: `K ∗ F(X)` embeds in
  `G(u, ℤⁿ)`.
* `TauCeti.LimitGroup.exists_ice_embedding_GX`: `H[X]` embeds over `H` in an ICE group over `H`.
* `TauCeti.LimitGroup.exists_ice_embedding_coprod_pi`: `H ∗ ℤⁿ` embeds over `H` in an ICE group
  over `H`.

## Implementation notes

Conjugated by `tᵢ g`, both homomorphisms send `k ∈ K` to `g⁻¹ tᵢ⁻¹ f(k) tᵢ g`. This is the single
letter `g⁻¹ f(k) g` of `G` when `f k ∈ C`, since `tᵢ` centralizes `C`, and it lies outside `C` by
malnormality. Otherwise it is the five letters `g⁻¹, tᵢ⁻¹, f k, tᵢ, g`. A nontrivial `a ∈ A` goes
to the single letter `a` of the factor `C × ℤⁿ`. A nontrivial `w ∈ F(X)`, written with syllables
`x₁^{e₁} ⋯ x_r^{e_r}` (consecutive `xⱼ` distinct, `eⱼ ≠ 0`), goes to the word
`tᵢ^{m x₁}, g, tᵢ^{e₁}, g⁻¹, tᵢ^{m x₂ - m x₁}, g, …, g⁻¹, tᵢ^{-m x_r}`. All these letters lie
outside the amalgamated subgroup, and the images of the letters of `K` start and end in `G` while
the others start and end in `C × ℤⁿ`. So the image of a nonempty reduced word of `K ∗ A` or
`K ∗ F(X)` (`Monoid.Coprod.exists_reduced_list_mk_eq`) is a nonempty reduced word of the amalgam,
which is not `1` by the normal form theorem (`Monoid.PushoutI.Reduced.eq_empty_of_mem_range`).

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
* J.-P. Serre, *Trees*, Chapter I, §1.2, Theorem 1 (the normal form theorem for amalgamated
  products).
-/

public section

open Monoid.Coprod Subgroup TauCeti.GroupAlgGeom

universe u

namespace TauCeti.LimitGroup

namespace CentralizerExt

open Monoid.PushoutI

variable {G : Type*} [Group G] {u : G} {n : ℕ}

/-! ### Reduced words of `G(u, ℤⁿ)` -/

/-- Left multiplication by `p` turns a reduced word of `G(u, ℤⁿ)` that does not start in the factor
`c` into the product of a reduced word that starts in the factor `b`: `p` behaves as a reduced word
from the factor `b` to the factor `c`. -/
private def IsBlock (b c : Bool) (p : CentralizerExt u n) : Prop :=
  ∀ W : Monoid.CoprodI.Word (CentralizerExtFactor u n), Reduced (centralizerExtMap u n) W →
    W.fstIdx ≠ some c → ∃ W' : Monoid.CoprodI.Word (CentralizerExtFactor u n),
      Reduced (centralizerExtMap u n) W' ∧ W'.fstIdx = some b ∧
        ofCoprodI (φ := centralizerExtMap u n) W'.prod = p * ofCoprodI W.prod

/-- A letter outside the amalgamated subgroup is a block of its own factor. -/
private theorem isBlock_of {b : Bool} {m : CentralizerExtFactor u n b}
    (hm : m ∉ (centralizerExtMap u n b).range) : IsBlock b b (Monoid.PushoutI.of b m) := by
  refine fun W hW hb => ⟨.cons m W hb fun h => hm (h ▸ one_mem _), fun l hl => ?_, by simp,
    by simp⟩
  rcases List.mem_cons.1 hl with rfl | hl
  exacts [hm, hW l hl]

/-- A block ending in one factor followed by a block starting in the other is a block. -/
private theorem IsBlock.mul {b c d : Bool} {p q : CentralizerExt u n} (hp : IsBlock b c p)
    (hq : IsBlock (!c) d q) : IsBlock b d (p * q) := by
  intro W hW hd
  obtain ⟨W₁, h₁, h₁i, h₁p⟩ := hq W hW hd
  obtain ⟨W₂, h₂, h₂i, h₂p⟩ := hp W₁ h₁ (by simp [h₁i])
  exact ⟨W₂, h₂, h₂i, by rw [h₂p, h₁p, mul_assoc]⟩

/-- An element of `G` outside `C_G(u)` is a one-letter block. -/
private theorem isBlock_of_notMem {x : G} (hx : x ∉ centralizer {u}) :
    IsBlock false false (of x : CentralizerExt u n) := by
  refine of_def (u := u) (n := n) ▸ isBlock_of fun ⟨c, hc⟩ => hx ?_
  rw [← hc, centralizerExtMap_false]
  exact c.2

/-- A nontrivial element `v` of `ℤⁿ`, the letter `(1, v)` of `C_G(u) × ℤⁿ`, is a one-letter
block. -/
private theorem isBlock_zpowersPiHom {v : Fin n → Multiplicative ℤ} (hv : v ≠ 1) :
    IsBlock true true (zpowersPiHom t commute_t_t v : CentralizerExt u n) := by
  have h := pushoutI_of_true (u := u) 1 v
  rw [OneMemClass.coe_one, map_one, one_mul] at h
  refine h ▸ isBlock_of fun ⟨c, hc⟩ => hv ?_
  rw [centralizerExtMap_true] at hc
  exact (congrArg Prod.snd hc).symm

/-- A nonzero power of `tᵢ` is a one-letter block. -/
private theorem isBlock_t_zpow (i : Fin n) {k : ℤ} (hk : k ≠ 0) :
    IsBlock true true (t i ^ k : CentralizerExt u n) := by
  rw [← zpowersPiHom_mulSingle t commute_t_t i, ← map_zpow]
  exact isBlock_zpowersPiHom (by simpa using hk)

/-- For `x ≠ 1`, the conjugate `(tᵢ g)⁻¹ x (tᵢ g)` is a block of `G`: the single letter `g⁻¹ x g`,
outside `C_G(u)` by malnormality, if `x ∈ C_G(u)`, and the five letters `g⁻¹, tᵢ⁻¹, x, tᵢ, g`
otherwise. -/
private theorem isBlock_conj (hC : TauCeti.IsTISubgroup (centralizer {u})) {g : G}
    (hg : g ∉ centralizer {u}) (i : Fin n) {x : G} (hx : x ≠ 1) :
    IsBlock (u := u) false false ((t i * of g)⁻¹ * of x * (t i * of g)) := by
  have hg' : g⁻¹ ∉ centralizer {u} := mt inv_mem_iff.1 hg
  by_cases hxC : x ∈ centralizer {u}
  · -- `tᵢ` commutes with `x ∈ C_G(u)`, so the conjugate is `of (g⁻¹ * x * g)`.
    have hc : (t i)⁻¹ * of x * t i = (of x : CentralizerExt u n) := by
      rw [mul_assoc, (commute_of_t (n := n) hxC i).eq, inv_mul_cancel_left]
    have hconj : (t i * of g)⁻¹ * of x * (t i * of g) =
        (of g)⁻¹ * ((t i)⁻¹ * of x * t i) * (of g : CentralizerExt u n) := by
      group
    rw [hconj, hc, ← map_inv, ← map_mul, ← map_mul]
    exact isBlock_of_notMem fun h => hx <|
      TauCeti.isTISubgroup_iff.1 hC (g := g⁻¹) hg' hxC (by simpa using h)
  · have h : (t i * of g)⁻¹ * of x * (t i * of g) =
        (of g⁻¹ * (t i ^ (-1 : ℤ) * (of x * (t i ^ (1 : ℤ) * of g))) : CentralizerExt u n) := by
      rw [map_inv]
      group
    rw [h]
    exact (isBlock_of_notMem hg').mul <| (isBlock_t_zpow i (by decide)).mul <|
      (isBlock_of_notMem hxC).mul <| (isBlock_t_zpow i one_ne_zero).mul (isBlock_of_notMem hg)

/-! ### Free products -/

section Lift

variable {K A : Type*} [Group K] [Group A]

/-- The homomorphism `K ∗ A →* G(u, ℤⁿ)` that is `ψ` on `A` and sends `k ∈ K` to
`(tᵢ g)⁻¹ f(k) (tᵢ g)`. -/
private def conjLift (f : K →* G) (ψ : A →* CentralizerExt u n) (g : G) (i : Fin n) :
    Monoid.Coprod K A →* CentralizerExt u n :=
  Monoid.Coprod.lift ((MulAut.conj (t i * of g)⁻¹).toMonoidHom.comp (of.comp f)) ψ

section

variable {f : K →* G} {ψ : A →* CentralizerExt u n} {g : G}

/-- `conjLift` sends a reduced word of `K ∗ A` to the product of a reduced word of `G(u, ℤⁿ)`
starting in the factor of its first letter, if the images of the nontrivial elements of `A` are
blocks of `C_G(u) × ℤⁿ`. -/
private theorem exists_reduced_conjLift (i : Fin n) (hf : Function.Injective f)
    (hC : TauCeti.IsTISubgroup (centralizer {u})) (hg : g ∉ centralizer {u})
    (hψ : ∀ a, a ≠ 1 → IsBlock true true (ψ a)) :
    ∀ L : List (K ⊕ A), (L.map Sum.isRight).IsChain (· ≠ ·) → Sum.inl 1 ∉ L → Sum.inr 1 ∉ L →
      ∃ W : Monoid.CoprodI.Word (CentralizerExtFactor u n), Reduced (centralizerExtMap u n) W ∧
        W.fstIdx = L.head?.map Sum.isRight ∧ ofCoprodI (φ := centralizerExtMap u n) W.prod =
          conjLift f ψ g i (mk (FreeMonoid.ofList L))
  | [], _, _, _ => ⟨.empty, fun _ h => by simp at h, rfl, by simp⟩
  | s :: L, hc, h₁, h₂ => by
    obtain ⟨W, hW, hWi, hWp⟩ := exists_reduced_conjLift i hf hC hg hψ L (by simpa using hc.tail)
      (fun h => h₁ (List.mem_cons_of_mem _ h)) fun h => h₂ (List.mem_cons_of_mem _ h)
    -- The first letter of `L` lies in the other factor.
    have hne : W.fstIdx ≠ some s.isRight := by
      have := (List.isChain_cons.1 (by simpa using hc)).1
      rw [hWi]
      cases L with
      | nil => simp
      | cons s' L => simpa [eq_comm] using this
    rw [FreeMonoid.ofList_cons, map_mul, map_mul, ← hWp]
    cases s with
    | inr a => simpa [conjLift] using hψ a (fun h => h₂ (h ▸ List.mem_cons_self)) W hW hne
    | inl k =>
      have hk : f k ≠ 1 := (map_ne_one_iff f hf).2 fun h => h₁ (h ▸ List.mem_cons_self)
      have hl : conjLift f ψ g i (mk (.of (.inl k))) =
          (t i * of g)⁻¹ * of (f k) * (t i * of g) := by
        simp [conjLift, mul_assoc]
      rw [hl]
      exact isBlock_conj hC hg i hk W hW hne

/-- The homomorphism `K ∗ A →* G(u, ℤⁿ)` that is `f` on `K` and `(tᵢ g) ψ (tᵢ g)⁻¹` on `A` is
injective if the images under `ψ` of the nontrivial elements of `A` are blocks of `C_G(u) × ℤⁿ`:
the image of a nonempty reduced word of `K ∗ A`, conjugated by `tᵢ g`, is the product of a nonempty
reduced word of the amalgam, which is not `1`. -/
private theorem injective_lift_conj (i : Fin n) (hf : Function.Injective f)
    (hC : TauCeti.IsTISubgroup (centralizer {u})) (hg : g ∉ centralizer {u})
    (hψ : ∀ a, a ≠ 1 → IsBlock true true (ψ a)) :
    Function.Injective
      (Monoid.Coprod.lift (of.comp f) ((MulAut.conj (t i * of g)).toMonoidHom.comp ψ)) := by
  have h : Monoid.Coprod.lift (of.comp f) ((MulAut.conj (t i * of g)).toMonoidHom.comp ψ) =
      (MulAut.conj (t i * of g)).toMonoidHom.comp (conjLift f ψ g i) := by
    ext <;> simp [conjLift, mul_assoc]
  rw [h, MonoidHom.coe_comp]
  refine (MulAut.conj _).injective.comp <| (injective_iff_map_eq_one _).2 fun x hx => ?_
  obtain ⟨L, hc, h₁, h₂, rfl⟩ := exists_reduced_list_mk_eq x
  obtain ⟨W, hW, hWi, hWp⟩ := exists_reduced_conjLift i hf hC hg hψ L hc h₁ h₂
  obtain rfl := hW.eq_empty_of_mem_range (centralizerExtMap_injective u n) ⟨1, by
    rw [map_one, hWp, hx]⟩
  cases L with
  | nil => rfl
  | cons s L => simp [Monoid.CoprodI.Word.fstIdx] at hWi

end

variable (u) in
/-- The homomorphism `K ∗ A →* G(u, ℤⁿ)` that is `f` on `K` and sends `a ∈ A` to the conjugate
`(tᵢ g) (ι a) (tᵢ g)⁻¹` of the element `ι a` of `ℤⁿ`. -/
def coprodPiLift (f : K →* G) (ι : A →* (Fin n → Multiplicative ℤ)) (g : G) (i : Fin n) :
    Monoid.Coprod K A →* CentralizerExt u n :=
  Monoid.Coprod.lift (of.comp f)
    ((MulAut.conj (t i * of g)).toMonoidHom.comp ((zpowersPiHom t commute_t_t).comp ι))

variable (u) (f : K →* G) (ι : A →* (Fin n → Multiplicative ℤ)) (g : G) (i : Fin n)

@[simp] theorem coprodPiLift_inl (k : K) : coprodPiLift u f ι g i (inl k) = of (f k) := by
  simp [coprodPiLift]

@[simp] theorem coprodPiLift_inr (a : A) :
    coprodPiLift u f ι g i (inr a) =
      t i * of g * zpowersPiHom t commute_t_t (ι a) * (t i * of g)⁻¹ := by
  simp only [coprodPiLift, lift_apply_inr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]

@[simp] theorem coprodPiLift_comp_inl : (coprodPiLift u f ι g i).comp inl = of.comp f :=
  Monoid.Coprod.lift_comp_inl _ _

variable {u f ι g}

/-- If `C_G(u)` is malnormal and `g ∉ C_G(u)`, then for embeddings `f : K →* G` and
`ι : A →* ℤⁿ` the homomorphism `K ∗ A →* G(u, ℤⁿ)` that is `f` on `K` and sends `a ∈ A` to
`(tᵢ g) (ι a) (tᵢ g)⁻¹` is injective. -/
theorem coprodPiLift_injective (hf : Function.Injective f) (hι : Function.Injective ι)
    (hC : TauCeti.IsTISubgroup (centralizer {u})) (hg : g ∉ centralizer {u}) :
    Function.Injective (coprodPiLift u f ι g i) :=
  injective_lift_conj i hf hC hg fun _ ha => isBlock_zpowersPiHom ((map_ne_one_iff ι hι).2 ha)

end Lift

section FreeGroup

variable {K X : Type*} [Group K]

variable (u) in
/-- The homomorphism `∗ₓ F(x) →* G(u, ℤⁿ)` that conjugates the factor `F(x)`, sent to `⟨tᵢ⟩`,
by `tᵢ^{m x} g`. -/
private def syllableLift (m : X → ℤ) (g : G) (i : Fin n) :
    (Monoid.CoprodI fun _ : X => FreeGroup Unit) →* CentralizerExt u n :=
  Monoid.CoprodI.lift fun x =>
    (MulAut.conj (t i ^ m x * of g)).toMonoidHom.comp (FreeGroup.lift fun _ => t i)

section

variable {m : X → ℤ} {g : G} (i : Fin n)

/-- The image under `syllableLift` of the product of a reduced word of `∗ₓ F(x)`, multiplied on the
left by `tᵢ^{-k}`, is a block of `C_G(u) × ℤⁿ`, provided that it is not `tᵢ⁰` and that `m` does not
take the value `k` on the first syllable. -/
private theorem isBlock_zpow_mul_syllableLift (hm : Function.Injective m) (hm₀ : ∀ x, m x ≠ 0)
    (hg : g ∉ centralizer {u}) (W : Monoid.CoprodI.Word fun _ : X => FreeGroup Unit) (k : ℤ)
    (hk₀ : W.fstIdx = none → k ≠ 0) (hk : ∀ x, W.fstIdx = some x → m x ≠ k) :
    IsBlock true true (t i ^ (-k) * syllableLift u m g i W.prod) := by
  induction W using Monoid.CoprodI.Word.consRecOn generalizing k with
  | empty => simpa using isBlock_t_zpow i (neg_ne_zero.2 (hk₀ rfl))
  | cons x z W h₁ h₂ ih =>
    obtain ⟨e, rfl⟩ : ∃ e : ℤ, FreeGroup.of () ^ e = z :=
      ⟨FreeGroup.freeGroupUnitEquivInt z, FreeGroup.freeGroupUnitEquivInt.symm_apply_apply z⟩
    have he : e ≠ 0 := by rintro rfl; exact h₂ (zpow_zero _)
    -- The syllable `x ^ e` gives the letters `tᵢ^{m x - k}, g, tᵢ^e, g⁻¹`, then `tᵢ^{-m x}`
    -- merges with the image of the rest of the word.
    have hx : t i ^ (-k) * syllableLift u m g i (Monoid.CoprodI.Word.cons _ W h₁ h₂).prod =
        t i ^ (m x - k) * (of g * (t i ^ e * (of g⁻¹ * (t i ^ (-m x) *
          syllableLift u m g i W.prod)))) := by
      rw [Monoid.CoprodI.Word.prod_cons, map_mul, syllableLift, Monoid.CoprodI.lift_of,
        MonoidHom.comp_apply, map_zpow (FreeGroup.lift fun _ => t i), FreeGroup.lift_apply_of,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_inv]
      group
    rw [hx]
    refine (isBlock_t_zpow i (sub_ne_zero.2 (hk x (Monoid.CoprodI.Word.fstIdx_cons ..)))).mul <|
      (isBlock_of_notMem hg).mul <| (isBlock_t_zpow i he).mul <|
        (isBlock_of_notMem (mt inv_mem_iff.1 hg)).mul <|
          ih (m x) (fun _ => hm₀ x) fun y hy hyx => h₁ ?_
    rwa [hm hyx] at hy

/-- The image of a nontrivial element of `F(X)` under `x ↦ (tᵢ^{m x} g) tᵢ (tᵢ^{m x} g)⁻¹` is a
block of `C_G(u) × ℤⁿ`, for `m` injective with nonzero values. -/
private theorem isBlock_freeGroupLift (hm : Function.Injective m) (hm₀ : ∀ x, m x ≠ 0)
    (hg : g ∉ centralizer {u}) {w : FreeGroup X} (hw : w ≠ 1) :
    IsBlock true true
      (FreeGroup.lift (fun x => MulAut.conj (t i ^ m x * of g) (t i : CentralizerExt u n)) w) := by
  classical
  have h : FreeGroup.lift (fun x => MulAut.conj (t i ^ m x * of g) (t i : CentralizerExt u n)) =
      (syllableLift u m g i).comp freeGroupEquivCoprodI.toMonoidHom := by
    ext
    simp [syllableLift]
  -- Write `w` as a reduced word in the syllables `x ^ e`.
  set W := Monoid.CoprodI.Word.equiv (freeGroupEquivCoprodI w)
  have hW : W.prod = freeGroupEquivCoprodI w := Monoid.CoprodI.Word.equiv.symm_apply_apply _
  have h₀ : W.fstIdx ≠ none := fun h₀ => hw <| freeGroupEquivCoprodI.injective <| by
    rw [← hW, map_one, Monoid.CoprodI.Word.prod, List.map_eq_nil_iff.2
      (List.head?_eq_none_iff.1 (Option.map_eq_none_iff.1 h₀)), List.prod_nil]
  rw [h, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hW]
  simpa using isBlock_zpow_mul_syllableLift i hm hm₀ hg W 0 (absurd · h₀) fun x _ => hm₀ x

end

variable (u) in
/-- The homomorphism `K ∗ F(X) →* G(u, ℤⁿ)` that is `f` on `K` and sends the generator `x` to the
conjugate `(tᵢ g tᵢ^{m x} g) tᵢ (tᵢ g tᵢ^{m x} g)⁻¹` of `tᵢ`, written as the conjugate by `tᵢ g`
of `(tᵢ^{m x} g) tᵢ (tᵢ^{m x} g)⁻¹`. -/
def coprodFreeGroupLift (f : K →* G) (m : X → ℤ) (g : G) (i : Fin n) :
    Monoid.Coprod K (FreeGroup X) →* CentralizerExt u n :=
  Monoid.Coprod.lift (of.comp f) ((MulAut.conj (t i * of g)).toMonoidHom.comp
    (FreeGroup.lift fun x => MulAut.conj (t i ^ m x * of g) (t i)))

variable (u) (f : K →* G) (m : X → ℤ) (g : G) (i : Fin n)

@[simp] theorem coprodFreeGroupLift_inl (k : K) :
    coprodFreeGroupLift u f m g i (inl k) = of (f k) := by
  simp [coprodFreeGroupLift]

@[simp] theorem coprodFreeGroupLift_inr_of (x : X) :
    coprodFreeGroupLift u f m g i (inr (.of x)) =
      t i * of g * (t i ^ m x * of g * t i * (t i ^ m x * of g)⁻¹) * (t i * of g)⁻¹ := by
  simp only [coprodFreeGroupLift, lift_apply_inr, MonoidHom.comp_apply, FreeGroup.lift_apply_of,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

@[simp] theorem coprodFreeGroupLift_comp_inl :
    (coprodFreeGroupLift u f m g i).comp inl = of.comp f :=
  Monoid.Coprod.lift_comp_inl _ _

variable {u f m g}

/-- If `C_G(u)` is malnormal and `g ∉ C_G(u)`, then for an embedding `f : K →* G` and an injective
`m : X → ℤ` with nonzero values, the homomorphism `K ∗ F(X) →* G(u, ℤⁿ)` that is `f` on `K` and
sends `x` to `(tᵢ g tᵢ^{m x} g) tᵢ (tᵢ g tᵢ^{m x} g)⁻¹` is injective. -/
theorem coprodFreeGroupLift_injective (hf : Function.Injective f) (hm : Function.Injective m)
    (hm₀ : ∀ x, m x ≠ 0) (hC : TauCeti.IsTISubgroup (centralizer {u}))
    (hg : g ∉ centralizer {u}) : Function.Injective (coprodFreeGroupLift u f m g i) :=
  injective_lift_conj i hf hC hg fun _ hw => isBlock_freeGroupLift i hm hm₀ hg hw

end FreeGroup

end CentralizerExt

open CentralizerExt

variable {H : Type u} [Group H]

/-- Over a nonabelian fully residually free group `H`, the free product `H ∗ ℤⁿ` embeds, over
`H`, in an iterated extension of centralizers of `H`. -/
theorem exists_ice_embedding_coprod_pi (hH : IsFullyResiduallyFree H) (hH' : ¬IsMulCommutative H)
    (n : ℕ) : ∃ (E : Type u) (_ : Group E) (j : H →* E) (_ : ICE H E j)
      (f : GHom (inl : H →* Monoid.Coprod H (Fin n → Multiplicative ℤ)) j),
      Function.Injective f := by
  rcases n with _ | n
  · -- `H ∗ ℤ⁰ ≃* H`, the second factor being trivial.
    let e : Monoid.Coprod H (Fin 0 → Multiplicative ℤ) ≃* H :=
      (MulEquiv.coprodCongr (.refl H) (MulEquiv.ofUnique (N := PUnit.{1}))).trans
        (MulEquiv.coprodPUnit H)
    exact ⟨H, _, .id H, .refl, .ofMulEquiv e fun h => by simp [e],
      (GHom.ofMulEquiv_bijective _ _).1⟩
  · obtain ⟨u, g, hu, hg⟩ := hH.isResiduallyFree.exists_not_isProperPower_notMem_centralizer hH'
    exact ⟨_, _, of, ICE.single (isAdmissibleCentralizerStep_iff.2 ⟨hu, n.succ_pos⟩),
      ⟨coprodPiLift u (.id H) (.id _) g 0, fun h => by simp⟩,
      coprodPiLift_injective 0 Function.injective_id Function.injective_id
        (hH.isCSA.centralizer_isTISubgroup u) hg⟩

/-- Over a nonabelian fully residually free group `H`, the free `H`-group `H[X] = H ∗ F(X)` on a
countable set embeds, over `H`, in an iterated extension of centralizers of `H`. -/
theorem exists_ice_embedding_GX (hH : IsFullyResiduallyFree H) (hH' : ¬IsMulCommutative H)
    (X : Type*) [Countable X] : ∃ (E : Type u) (_ : Group E) (j : H →* E) (_ : ICE H E j)
      (f : GHom (inl : H →* GX H X) j), Function.Injective f := by
  obtain ⟨u, g, hu, hg⟩ := hH.isResiduallyFree.exists_not_isProperPower_notMem_centralizer hH'
  obtain ⟨e, he⟩ := Countable.exists_injective_nat X
  refine ⟨_, _, of, ICE.single (isAdmissibleCentralizerStep_iff.2 ⟨hu, Nat.one_pos⟩),
    ⟨coprodFreeGroupLift u (.id H) (fun x => e x + 1) g (0 : Fin 1), fun h => by simp⟩,
    coprodFreeGroupLift_injective 0 Function.injective_id (fun x y h => he (by simpa using h))
      (fun x => by omega) (hH.isCSA.centralizer_isTISubgroup u) hg⟩

end TauCeti.LimitGroup
