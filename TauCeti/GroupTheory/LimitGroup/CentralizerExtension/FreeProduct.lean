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

Let `H` be a nonabelian fully residually free group. The free `H`-group `H[X] = H ∗ F(X)` on a
finite set `X` and the free product `H ∗ ℤⁿ` embed, over `H`, in iterated extensions of centralizers
of `H`. These are the free and the free abelian levels of a normalized tower over `H`.

Both embeddings come from one construction. Let `u` be an element of a group `G` whose centralizer
`C = C_G(u)` is malnormal, as in every CSA group, let `g ∉ C`, and let `tᵢ` be a new letter of the
extension `G(u, ℤⁿ) = G ∗_C (C × ℤⁿ)`. For an embedding `f : K →* G` and a subgroup `A` of `ℤⁿ`,
the homomorphism `K ∗ A →* G(u, ℤⁿ)` that is `f` on `K` and sends `a ∈ A` to the conjugate
`(tᵢ g) a (tᵢ g)⁻¹` is injective. For `H ∗ ℤⁿ` take `K = H` and `A = ℤⁿ`, which gives a one-step
chain. For `H[X]` add one variable at a time, with `A = ℤ`, to the group reached so far, which is
again nonabelian and fully residually free. The element `u` is chosen not to be a proper power, by
root reduction, so that each step is admissible.

## Main results

* `TauCeti.LimitGroup.exists_ice_embedding_GX`: `H[X]` embeds over `H` in an ICE group over `H`.
* `TauCeti.LimitGroup.exists_ice_embedding_coprod_pi`: `H ∗ ℤⁿ` embeds over `H` in an ICE group
  over `H`.

## Implementation notes

Conjugated by `tᵢ g`, the homomorphism above sends `a ∈ A` to the letter `a` of the factor
`C × ℤⁿ`, and `k ∈ K` to `g⁻¹ tᵢ⁻¹ f(k) tᵢ g`. This is the single letter `g⁻¹ f(k) g` of `G` when
`f k ∈ C`, since `tᵢ` centralizes `C`, and it lies outside `C` by malnormality. Otherwise it is the
five letters `g⁻¹, tᵢ⁻¹, f k, tᵢ, g`. All these letters lie outside the amalgamated subgroup, and
the images of the letters of `K` start and end in `G`. So the image of a nonempty reduced word of
`K ∗ A` (`Monoid.Coprod.exists_reduced_list_mk_eq`) is a nonempty reduced word of the amalgam,
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

/-- Prepending a letter outside the amalgamated subgroup to a reduced word of `G(u, ℤⁿ)` that does
not start in the same factor gives a reduced word. -/
private theorem exists_reduced_of_mul {b : Bool} (m : CentralizerExtFactor u n b)
    (hm : m ∉ (centralizerExtMap u n b).range) {W : Monoid.CoprodI.Word (CentralizerExtFactor u n)}
    (hW : Reduced (centralizerExtMap u n) W) (hb : W.fstIdx ≠ some b) :
    ∃ W' : Monoid.CoprodI.Word (CentralizerExtFactor u n), Reduced (centralizerExtMap u n) W' ∧
      W'.fstIdx = some b ∧
      ofCoprodI (φ := centralizerExtMap u n) W'.prod =
        Monoid.PushoutI.of b m * ofCoprodI W.prod := by
  refine ⟨.cons m W hb fun h => hm (h ▸ one_mem _), fun l hl => ?_, by simp, by simp⟩
  rcases List.mem_cons.1 hl with rfl | hl
  exacts [hm, hW l hl]

/-- A letter `(c, v)` of `C_G(u) × ℤⁿ` with `v ≠ 1` is not in the amalgamated subgroup. -/
private theorem notMem_range_true {v : Fin n → Multiplicative ℤ} (hv : v ≠ 1)
    (c : centralizer {u}) :
    ((c, v) : centralizer {u} × (Fin n → Multiplicative ℤ)) ∉
      (centralizerExtMap u n true).range := by
  rintro ⟨c', hc⟩
  rw [centralizerExtMap_true] at hc
  exact hv (congrArg Prod.snd hc).symm

/-- A letter of `G` outside `C_G(u)` is not in the amalgamated subgroup. -/
private theorem notMem_range_false {x : G} (hx : x ∉ centralizer {u}) :
    x ∉ (centralizerExtMap u n false).range := by
  rintro ⟨c, rfl⟩
  rw [centralizerExtMap_false] at hx
  exact hx c.2

/-! ### Free products with subgroups of `ℤⁿ` -/

section Conj

variable (u) {g : G} (i : Fin n)

/-- The homomorphism `K ∗ A →* G(u, ℤⁿ)` that sends `a ∈ A` to the letter `ι a` of `ℤⁿ` and
`k ∈ K` to the conjugate `(tᵢ g)⁻¹ f(k) (tᵢ g)`. Conjugated by `tᵢ g`, it is `f` on `K`. -/
private def conjLift {K A : Type*} [Group K] [Group A] (f : K →* G)
    (ι : A →* (Fin n → Multiplicative ℤ)) (g : G) (i : Fin n) :
    Monoid.Coprod K A →* CentralizerExt u n :=
  Monoid.Coprod.lift ((MulAut.conj (t i * of g)⁻¹).toMonoidHom.comp (of.comp f))
    ((zpowersPiHom t commute_t_t).comp ι)

variable {u}

/-- The image `(tᵢ g)⁻¹ x (tᵢ g)` of an element `x ≠ 1` of `C_G(u)` is the single letter
`g⁻¹ x g` of `G`, outside `C_G(u)` by malnormality. -/
private theorem exists_reduced_conj_mul_of_mem (hC : TauCeti.IsTISubgroup (centralizer {u}))
    (hg : g ∉ centralizer {u}) {x : G} (hx : x ∈ centralizer {u}) (hx1 : x ≠ 1)
    {W : Monoid.CoprodI.Word (CentralizerExtFactor u n)} (hW : Reduced (centralizerExtMap u n) W)
    (hb : W.fstIdx ≠ some false) :
    ∃ W' : Monoid.CoprodI.Word (CentralizerExtFactor u n), Reduced (centralizerExtMap u n) W' ∧
      W'.fstIdx = some false ∧ ofCoprodI (φ := centralizerExtMap u n) W'.prod =
        (t i * of g)⁻¹ * of x * (t i * of g) * ofCoprodI W.prod := by
  have hm : g⁻¹ * x * g ∉ centralizer {u} := fun h => hx1 <|
    TauCeti.isTISubgroup_iff.1 hC (g := g⁻¹) (fun h' => hg (by simpa using inv_mem h')) hx
      (by simpa using h)
  obtain ⟨W', hW', hW'i, hW'p⟩ := exists_reduced_of_mul (b := false) _ (notMem_range_false hm) hW hb
  refine ⟨W', hW', hW'i, ?_⟩
  -- `tᵢ` commutes with `x ∈ C_G(u)`, so the conjugate is `of (g⁻¹ * x * g)`.
  have hc : (t i)⁻¹ * of x * t i = (of x : CentralizerExt u n) := by
    rw [mul_assoc, (commute_of_t (n := n) hx i).eq, inv_mul_cancel_left]
  have hconj : (t i * of g)⁻¹ * of x * (t i * of g) =
      (of g)⁻¹ * ((t i)⁻¹ * of x * t i) * (of g : CentralizerExt u n) := by
    group
  rw [hW'p, hconj, hc, ← of_def, map_mul, map_mul, map_inv]

/-- The image `(tᵢ g)⁻¹ x (tᵢ g)` of an element `x ∉ C_G(u)` is the reduced word
`g⁻¹, tᵢ⁻¹, x, tᵢ, g`. -/
private theorem exists_reduced_conj_mul_of_notMem (hg : g ∉ centralizer {u}) {x : G}
    (hx : x ∉ centralizer {u}) {W : Monoid.CoprodI.Word (CentralizerExtFactor u n)}
    (hW : Reduced (centralizerExtMap u n) W) (hb : W.fstIdx ≠ some false) :
    ∃ W' : Monoid.CoprodI.Word (CentralizerExtFactor u n), Reduced (centralizerExtMap u n) W' ∧
      W'.fstIdx = some false ∧ ofCoprodI (φ := centralizerExtMap u n) W'.prod =
        (t i * of g)⁻¹ * of x * (t i * of g) * ofCoprodI W.prod := by
  have he : (Pi.mulSingle i (.ofAdd 1) : Fin n → Multiplicative ℤ) ≠ 1 := by simp
  have hg' : g⁻¹ ∉ centralizer {u} := fun h => hg (by simpa using inv_mem h)
  obtain ⟨W₁, h₁, h₁i, h₁p⟩ := exists_reduced_of_mul (b := false) g (notMem_range_false hg) hW hb
  obtain ⟨W₂, h₂, h₂i, h₂p⟩ := exists_reduced_of_mul (b := true) _ (notMem_range_true he 1) h₁
    (by simp [h₁i])
  obtain ⟨W₃, h₃, h₃i, h₃p⟩ := exists_reduced_of_mul (b := false) x (notMem_range_false hx) h₂
    (by simp [h₂i])
  obtain ⟨W₄, h₄, h₄i, h₄p⟩ := exists_reduced_of_mul (b := true)
    (((1 : centralizer {u}), Pi.mulSingle i (.ofAdd 1)) : CentralizerExtFactor u n true)⁻¹
    (fun h => notMem_range_true he 1 (inv_mem_iff.1 h)) h₃ (by simp [h₃i])
  obtain ⟨W₅, h₅, h₅i, h₅p⟩ := exists_reduced_of_mul (b := false) g⁻¹ (notMem_range_false hg') h₄
    (by simp [h₄i])
  refine ⟨W₅, h₅, h₅i, ?_⟩
  rw [h₅p, h₄p, h₃p, h₂p, h₁p, ← of_def, t_def, map_inv]
  simp [mul_assoc]

variable {K A : Type*} [Group K] [Group A] {f : K →* G} {ι : A →* (Fin n → Multiplicative ℤ)}

/-- `conjLift` sends a reduced word of `K ∗ A` to the product of a reduced word of `G(u, ℤⁿ)`
starting in the factor of its first letter. -/
private theorem exists_reduced_conjLift (hf : Function.Injective f) (hι : Function.Injective ι)
    (hC : TauCeti.IsTISubgroup (centralizer {u})) (hg : g ∉ centralizer {u}) :
    ∀ L : List (K ⊕ A), (L.map Sum.isRight).IsChain (· ≠ ·) → Sum.inl 1 ∉ L → Sum.inr 1 ∉ L →
      ∃ W : Monoid.CoprodI.Word (CentralizerExtFactor u n), Reduced (centralizerExtMap u n) W ∧
        W.fstIdx = L.head?.map Sum.isRight ∧ ofCoprodI (φ := centralizerExtMap u n) W.prod =
          conjLift u f ι g i (mk (FreeMonoid.ofList L))
  | [], _, _, _ => ⟨.empty, fun _ h => by simp at h, rfl, by simp⟩
  | s :: L, hc, h₁, h₂ => by
    obtain ⟨W, hW, hWi, hWp⟩ := exists_reduced_conjLift hf hι hC hg L (by simpa using hc.tail)
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
    | inr a =>
      have ha : ι a ≠ 1 := (map_ne_one_iff ι hι).2 fun h => h₂ (h ▸ List.mem_cons_self)
      obtain ⟨W', hW', hW'i, hW'p⟩ :=
        exists_reduced_of_mul (b := true) _ (notMem_range_true ha 1) hW hne
      refine ⟨W', hW', hW'i, ?_⟩
      -- The letter `(1, ι a)` of `C_G(u) × ℤⁿ` is `∏ tⱼ ^ (ι a)ⱼ`.
      simpa [conjLift, pushoutI_of_true] using hW'p
    | inl k =>
      have hk : f k ≠ 1 := (map_ne_one_iff f hf).2 fun h => h₁ (h ▸ List.mem_cons_self)
      have hl : conjLift u f ι g i (mk (.of (.inl k))) =
          (t i * of g)⁻¹ * of (f k) * (t i * of g) := by
        simp [conjLift, mul_assoc]
      rw [hl]
      by_cases hkC : f k ∈ centralizer {u}
      · exact exists_reduced_conj_mul_of_mem i hC hg hkC hk hW hne
      · exact exists_reduced_conj_mul_of_notMem i hg hkC hW hne

/-- `conjLift` is injective: the image of a nonempty reduced word is the product of a nonempty
reduced word of the amalgam, which is not `1`. -/
private theorem conjLift_injective (hf : Function.Injective f) (hι : Function.Injective ι)
    (hC : TauCeti.IsTISubgroup (centralizer {u})) (hg : g ∉ centralizer {u}) :
    Function.Injective (conjLift u f ι g i) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  obtain ⟨L, hc, h₁, h₂, rfl⟩ := exists_reduced_list_mk_eq x
  obtain ⟨W, hW, hWi, hWp⟩ := exists_reduced_conjLift i hf hι hC hg L hc h₁ h₂
  obtain rfl := hW.eq_empty_of_mem_range (centralizerExtMap_injective u n) ⟨1, by
    rw [map_one, hWp, hx]⟩
  cases L with
  | nil => rfl
  | cons s L => simp [Monoid.CoprodI.Word.fstIdx] at hWi

end Conj

end CentralizerExt

open CentralizerExt

/-- A nonabelian residually free group has an element `u` that is not a proper power and an element
`g` outside `C(u)`. -/
private theorem exists_not_isProperPower_notMem_centralizer {G : Type*} [Group G]
    (hG : IsResiduallyFree G) (hG' : ¬IsMulCommutative G) :
    ∃ u g : G, ¬Group.IsProperPower u ∧ g ∉ centralizer {u} := by
  obtain ⟨a, b, hab⟩ : ∃ a b : G, b * a ≠ a * b := by
    by_contra! h
    exact hG' ⟨⟨fun a b => h b a⟩⟩
  obtain ⟨r, -, -, -, hr, hC⟩ := hG.centralizerExt_root_reduction (u := a)
    (by rintro rfl; simp at hab)
  exact ⟨r, b, hr, by rwa [← hC, mem_centralizer_singleton_iff]⟩

/-- Over a nonabelian fully residually free group `E`, for an embedding `f : K →* E` the free
product `K ∗ ℤⁿ⁺¹` embeds in an admissible extension `E(u, ℤⁿ⁺¹)`, by a homomorphism that is `f`
on `K`. -/
private theorem exists_injective_coprod_pi {E K : Type*} [Group E] [Group K]
    (hE : IsFullyResiduallyFree E) (hE' : ¬IsMulCommutative E) {f : K →* E}
    (hf : Function.Injective f) (n : ℕ) :
    ∃ (u : E) (_ : IsAdmissibleCentralizerStep u (n + 1))
      (F : Monoid.Coprod K (Fin (n + 1) → Multiplicative ℤ) →* CentralizerExt u (n + 1)),
      F.comp inl = of.comp f ∧ Function.Injective F := by
  obtain ⟨u, g, hu, hg⟩ := exists_not_isProperPower_notMem_centralizer hE.isResiduallyFree hE'
  refine ⟨u, isAdmissibleCentralizerStep_iff.2 ⟨hu, n.succ_pos⟩,
    (MulAut.conj (t 0 * of g)).toMonoidHom.comp (conjLift u f (.id _) g 0), ?_,
    (MulAut.conj _).injective.comp (conjLift_injective 0 hf Function.injective_id
      (hE.isCSA.centralizer_isTISubgroup u) hg)⟩
  ext k
  simp [conjLift, mul_assoc]

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
  · obtain ⟨u, hu, F, hF, hFi⟩ :=
      exists_injective_coprod_pi hH hH' (f := .id H) Function.injective_id n
    exact ⟨_, _, of, ICE.single hu, ⟨F, fun h => by simpa using DFunLike.congr_fun hF h⟩, hFi⟩

/-- `H[Option X]` is `H[X] ∗ ℤ` over `H`: the variable `none` goes to the generator of `ℤ`. -/
private def splitNone (X : Type*) :
    GX H (Option X) →* Monoid.Coprod (GX H X) (Fin 1 → Multiplicative ℤ) :=
  eval (inl.comp inl) fun o => o.elim (inr (Pi.mulSingle 0 (.ofAdd 1))) fun x => inl (inr (.of x))

private theorem splitNone_injective (X : Type*) : Function.Injective (splitNone (H := H) X) := by
  let τ : Monoid.Coprod (GX H X) (Fin 1 → Multiplicative ℤ) →* GX H (Option X) :=
    Monoid.Coprod.lift (Monoid.Coprod.map (.id H) (FreeGroup.map some))
      ((zpowersHom _ (inr (.of none))).comp (Pi.evalMonoidHom _ 0))
  have hτ : τ.comp (splitNone X) = .id _ := by
    refine Monoid.Coprod.hom_ext (by ext; simp [τ, splitNone]) (FreeGroup.ext_hom _ _ ?_)
    rintro (_ | x) <;> simp [τ, splitNone]
  exact Function.LeftInverse.injective (g := τ) (DFunLike.congr_fun hτ)

/-- The induction step for `exists_ice_embedding_GX`: one more variable needs one more admissible
extension of a centralizer. -/
private theorem exists_ice_embedding_GX_option (hH : IsFullyResiduallyFree H)
    (hH' : ¬IsMulCommutative H) {X : Type*} {E : Type u} [Group E] {j : H →* E} (c : ICE H E j)
    {f : GHom (inl : H →* GX H X) j} (hf : Function.Injective f) :
    ∃ (E' : Type u) (_ : Group E') (j' : H →* E') (_ : ICE H E' j')
      (f' : GHom (inl : H →* GX H (Option X)) j'), Function.Injective f' := by
  -- `E` is fully residually free and, containing `H`, nonabelian.
  have hE' : ¬IsMulCommutative E := fun h => hH' ⟨⟨fun a b => c.injective
    (by simp only [map_mul]; exact h.is_comm.comm _ _)⟩⟩
  obtain ⟨u, hu, F, hF, hFi⟩ :=
    exists_injective_coprod_pi (c.isFullyResiduallyFree hH) hE' (f := (f : GX H X →* E)) hf 0
  refine ⟨_, _, of.comp j, c.step hu, ⟨F.comp (splitNone X), fun h => ?_⟩,
    hFi.comp (splitNone_injective X)⟩
  simpa [splitNone] using DFunLike.congr_fun hF (inl h)

/-- Over a nonabelian fully residually free group `H`, the free `H`-group `H[X] = H ∗ F(X)` on a
finite set embeds, over `H`, in an iterated extension of centralizers of `H`. -/
theorem exists_ice_embedding_GX (hH : IsFullyResiduallyFree H) (hH' : ¬IsMulCommutative H)
    (X : Type*) [Finite X] : ∃ (E : Type u) (_ : Group E) (j : H →* E) (_ : ICE H E j)
      (f : GHom (inl : H →* GX H X) j), Function.Injective f := by
  induction X using Finite.induction_empty_option with
  | of_equiv e ih =>
    obtain ⟨E, _, j, c, f, hf⟩ := ih
    -- Rename the variables along `e`.
    let σ : GHom (inl : H →* GX H _) (inl : H →* GX H _) :=
      .ofMulEquiv (MulEquiv.coprodCongr (.refl H) (FreeGroup.freeGroupCongr e.symm)) fun h => by
        simp
    exact ⟨E, _, j, c, f.comp σ, by
      rw [GHom.coe_comp]
      exact hf.comp (GHom.ofMulEquiv_bijective _ _).1⟩
  | h_empty =>
    exact ⟨H, _, .id H, .refl, .ofMulEquiv GX.equivOfIsEmpty fun h => by simp,
      (GHom.ofMulEquiv_bijective _ _).1⟩
  | h_option ih =>
    obtain ⟨E, _, j, c, f, hf⟩ := ih
    exact exists_ice_embedding_GX_option hH hH' c hf

end TauCeti.LimitGroup
