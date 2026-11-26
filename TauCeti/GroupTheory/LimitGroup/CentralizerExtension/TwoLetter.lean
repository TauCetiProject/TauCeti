/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
import Mathlib.Tactic.Group
import TauCeti.GroupTheory.Coprod.Basic
import TauCeti.GroupTheory.Coprod.Centralizer
import TauCeti.GroupTheory.HNNExtension.Double
import TauCeti.GroupTheory.HNNExtension.FreeFactor
import TauCeti.GroupTheory.HNNExtension.Map
import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.HNN
import TauCeti.GroupTheory.LimitGroup.TwoGenerator
import TauCeti.GroupTheory.PushoutI.FreeFactor

/-!
# A free letter in two extensions of centralizers

Let `G` be a fully residually free group and `ρ`, `δ` two elements of `G` that do not commute.
Extend the centralizer of `ρ` by a letter `s`, and then the centralizer of `δ` in `G(ρ, s)` by a
letter `u`. The product `s u` is free over `G`: the homomorphism `G[z] → G(ρ, s)(δ, u)` sending
the variable `z` to `s u` is injective (`CentralizerExt.twoLetterHom_injective`). Its image is
therefore a free product of `G` with `⟨s u⟩`, and it contains the second copy `(s u)⁻¹ G (s u)` of
`G`, in which `ρ` becomes `(s u)⁻¹ ρ (s u) = u⁻¹ ρ u` since `s` commutes with `ρ`; this is the
device by which Kharlampovich and Myasnikov replace, one atom at a time, a solution of a quadratic
equation by a generic one. The same holds when the two centralizers are extended by free abelian
groups `ℤᵐ` and `ℤⁿ` of higher rank, for the product `sᵢ uⱼ` of any letter `sᵢ` of the first and
any letter `uⱼ` of the second extension.

The second letter extends the full centralizer of `δ` in `G(ρ, s)`, as an extension of a
centralizer of that group must. It is larger than `C_G(δ)` when `δ` is conjugate into `C_G(ρ)`; in
[VAR-I] the second letter extends `C_G(δ)` and that case is excluded by an assumption on the
conjugates of `C_G(δ)`, which is not needed here. The only input from full residual freeness is
that the centralizers of `ρ` and `δ` generate their free product
(`IsFullyResiduallyFree.coprodLift_subtype_centralizer_injective`, [VAR-I] Lemma 21), and the
injectivity holds for every group with that property
(`CentralizerExt.twoLetterHom_injective_of_injective`).

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt.twoLetterHom ρ δ i j`: the homomorphism
  `G[z] →* G(ρ, s)(δ, u)` over `G` sending `z` to `sᵢ uⱼ`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.twoLetterHom_conj_inv_apply`: for `g` commuting with `ρ`,
  the image of `z⁻¹ g z` is `(sᵢ uⱼ)⁻¹ g (sᵢ uⱼ) = uⱼ⁻¹ g uⱼ`.
* `TauCeti.LimitGroup.CentralizerExt.twoLetterHom_injective_of_injective`: if the centralizers of
  `ρ` and `δ` generate their free product in `G`, the homomorphism `twoLetterHom ρ δ i j` is
  injective.
* `TauCeti.LimitGroup.CentralizerExt.twoLetterHom_injective`: if `ρ` and `δ` do not commute in the
  fully residually free group `G`, the homomorphism `twoLetterHom ρ δ i j` is injective.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §5,
  Propositions 10–12 and Lemma 21.
-/

public section

open Monoid.Coprod Subgroup TauCeti.GroupAlgGeom

universe u

namespace TauCeti.LimitGroup

namespace CentralizerExt

variable {G : Type u} [Group G] {m n : ℕ}

/-- The homomorphism `G[z] → G(ρ, s)(δ, u)` over `G` sending the variable `z` to `sᵢ uⱼ`, where
`G(ρ, s)` extends the centralizer of `ρ` by `ℤᵐ` with new letters `s₀, …, s_{m-1}` and
`G(ρ, s)(δ, u)` extends the centralizer of `δ` in `G(ρ, s)` by `ℤⁿ` with new letters
`u₀, …, u_{n-1}`. -/
def twoLetterHom (ρ δ : G) (i : Fin m) (j : Fin n) :
    GX G Unit →* CentralizerExt (of δ : CentralizerExt ρ m) n :=
  eval (of.comp of) fun _ => of (t i) * t j

theorem twoLetterHom_def (ρ δ : G) (i : Fin m) (j : Fin n) :
    twoLetterHom ρ δ i j = eval (of.comp of) fun _ => of (t i) * t j :=
  (rfl)

@[simp]
theorem twoLetterHom_comp_inl (ρ δ : G) (i : Fin m) (j : Fin n) :
    (twoLetterHom ρ δ i j).comp inl = of.comp of :=
  eval_comp_inl ..

@[simp]
theorem twoLetterHom_comp_inr (ρ δ : G) (i : Fin m) (j : Fin n) :
    (twoLetterHom ρ δ i j).comp inr = FreeGroup.lift fun _ => of (t i) * t j :=
  eval_comp_inr ..

@[simp]
theorem twoLetterHom_inl (ρ δ : G) (i : Fin m) (j : Fin n) (g : G) :
    twoLetterHom ρ δ i j (inl g) = of (of g) := by
  simp [twoLetterHom]

@[simp]
theorem twoLetterHom_inr_of (ρ δ : G) (i : Fin m) (j : Fin n) (x : Unit) :
    twoLetterHom ρ δ i j (inr (FreeGroup.of x)) = of (t i) * t j := by
  simp [twoLetterHom]

/-- For `g` commuting with `ρ`, for instance `g = ρ`, the image of the conjugate `z⁻¹ g z` is
`(sᵢ uⱼ)⁻¹ g (sᵢ uⱼ) = uⱼ⁻¹ g uⱼ`: the letter `sᵢ` commutes with `g`. -/
@[simp]
theorem twoLetterHom_conj_inv_apply (ρ δ : G) (i : Fin m) (j : Fin n) {g : G}
    (hg : Commute g ρ) :
    twoLetterHom ρ δ i j ((inr (FreeGroup.of ()))⁻¹ * inl g * inr (FreeGroup.of ())) =
      (t j)⁻¹ * of (of g) * t j := by
  have hc : Commute (of (of g) : CentralizerExt (of δ : CentralizerExt ρ m) n) (of (t i)) :=
    (commute_of_t (mem_centralizer_singleton_iff.2 hg) i).map of
  simp only [map_mul, map_inv, twoLetterHom_inl, twoLetterHom_inr_of]
  calc (of (t i) * t j)⁻¹ * of (of g) * (of (t i) * t j)
      = (t j)⁻¹ * ((of (t i))⁻¹ * (of (of g) * of (t i))) * t j := by group
    _ = (t j)⁻¹ * of (of g) * t j := by rw [hc.eq, inv_mul_cancel_left]

/-- `simp` computes the image of the conjugate `z⁻¹ ρ z`. -/
example (ρ δ : G) (i : Fin m) (j : Fin n) :
    twoLetterHom ρ δ i j ((inr (FreeGroup.of ()))⁻¹ * inl ρ * inr (FreeGroup.of ())) =
      (t j)⁻¹ * of (of ρ) * t j := by
  simp

/-! ### Injectivity

Write `C = C_G(ρ)`, `Q = C_G(δ)` and `K = G(ρ, s)`. The homomorphism `θ : G ∗ Q →* K` that is the
inclusion on `G` and `q ↦ s q s⁻¹` on `Q` is injective when `C` and `Q` generate their free product
in `G` ([VAR-I] Lemma 21): `G ∗ Q` is the amalgam `G ∗_C (C ∗ Q)`
(`Monoid.PushoutI.freeFactorEquiv`), which embeds in the double `G ∗_C G`
(`Monoid.PushoutI.freeFactorToDouble_injective`), and the double embeds in `K`. In `G ∗ Q` the
centralizer of `δ` in the free factor `Q` is that factor, and the centralizer of `δ ∈ G` is the
copy of `Q` in `G` (`Monoid.Coprod.centralizer_inr_eq_map`, `Monoid.Coprod.centralizer_inl_eq_map`);
this needs `δ ≠ 1`, and for `δ = 1` the hypothesis forces `G = 1`, where `twoLetterHom` is
`ℤ → ℤ²`, `z ↦ (1, 1)`. The HNN extension of `G ∗ Q` along
`inr q ↦ inl q`, with relations `t q t⁻¹ = q` from the free factor to `G`, is `G[z]` with
`t = z⁻¹` (`HNNExtension.equivCoprodFreeGroup`). After `θ`, the identification `inr q ↦ inl q`
becomes `x ↦ s⁻¹ x s` from the image `s q s⁻¹` of the free factor to the image `q` of `G`, so the
HNN extension embeds in `K(θ δ, ℤ) = K(δ, ℤ)` by `θ` and `t ↦ (s u)⁻¹`
(`CentralizerExt.hnnLift_injective`). The composite `G[z] → K(δ, ℤ)` is `twoLetterHom ρ δ 0 0`.

For extensions by `ℤᵐ` and `ℤⁿ`, keeping the letters `sᵢ` and `uⱼ` and killing the others is a
homomorphism `G(ρ, ℤᵐ)(δ, ℤⁿ) → G(ρ, ℤ)(δ, ℤ)` over `G` that carries `twoLetterHom ρ δ i j` to
`twoLetterHom ρ δ 0 0`, so injectivity reduces to the rank-one case. -/

section Injective

open Monoid.PushoutI

variable (ρ δ : G)

/-- The homomorphism `θ : G ∗ C_G(δ) →* G(ρ, s)` that is the inclusion on `G` and `q ↦ s q s⁻¹` on
`C_G(δ)`. -/
private noncomputable def baseHom : G ∗ centralizer {δ} →* CentralizerExt ρ 1 :=
  (equivHNNExtension (u := ρ)).symm.toMonoidHom.comp <| (HNNExtension.ofDouble _).comp <|
    (freeFactorToDouble (centralizer {ρ}).subtype (centralizer {δ}).subtype).comp
      (freeFactorEquiv (centralizer {ρ}).subtype).symm.toMonoidHom

private theorem baseHom_inl (g : G) : baseHom ρ δ (inl g) = of g := by
  simp [baseHom]

private theorem baseHom_inr (q : centralizer {δ}) :
    baseHom ρ δ (inr q) = t 0 * of (q : G) * (t 0)⁻¹ := by
  simp [baseHom]

private theorem baseHom_injective
    (hinj : Function.Injective (Monoid.Coprod.lift (centralizer {ρ}).subtype
      (centralizer {δ}).subtype)) :
    Function.Injective (baseHom ρ δ) :=
  (equivHNNExtension (u := ρ)).symm.injective.comp <| (HNNExtension.ofDouble_injective _).comp <|
    (freeFactorToDouble_injective hinj).comp (freeFactorEquiv _).symm.injective

/-- The element `δ` of its centralizer `C_G(δ)`. -/
private abbrev deltaQ : centralizer {δ} :=
  ⟨δ, mem_centralizer_singleton_iff.2 (.refl δ)⟩

variable {δ}

/-- For `δ ≠ 1`, the centralizer in the free product `G ∗ C_G(δ)` of the copy `inr δ` of `δ` in the
free factor `C_G(δ)` is that free factor. -/
private theorem centralizer_inr_deltaQ (hδ : δ ≠ 1) :
    centralizer {(inr (deltaQ δ) : G ∗ centralizer {δ})} =
      (inr : centralizer {δ} →* G ∗ centralizer {δ}).range := by
  rw [centralizer_inr_eq_map fun h => hδ (congrArg Subtype.val h), MonoidHom.range_eq_map]
  -- Every element of `C_G(δ)` commutes with `δ`.
  exact congrArg _ <| eq_top_iff.2 fun (q : centralizer {δ}) _ =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 q.property))

/-- For `δ ≠ 1`, the centralizer in the free product `G ∗ C_G(δ)` of the copy `inl δ` of `δ` in `G`
is the copy of `C_G(δ)` in `G`. -/
private theorem centralizer_inl_delta (hδ : δ ≠ 1) :
    centralizer {(inl δ : G ∗ centralizer {δ})} = (inl.comp (centralizer {δ}).subtype).range := by
  rw [centralizer_inl_eq_map hδ, MonoidHom.range_comp, range_subtype]

/-- For `δ ≠ 1`, the isomorphism `inr q ↦ inl q` from the centralizer of `inr δ` in `G ∗ C_G(δ)`,
which is the free factor `C_G(δ)`, onto the centralizer of `inl δ` in `G ∗ C_G(δ)`, which is the
copy of `C_G(δ)` in `G`. -/
private noncomputable def hnnEquiv (hδ : δ ≠ 1) :
    centralizer {(inr (deltaQ δ) : G ∗ centralizer {δ})} ≃*
      centralizer {(inl δ : G ∗ centralizer {δ})} :=
  (MulEquiv.subgroupCongr (centralizer_inr_deltaQ hδ)).trans <|
    (MonoidHom.rangeEquivRange _ (inl.comp (centralizer {δ}).subtype)
      (MonoidHom.ker_eq_ker_of_injective inr_injective
        (inl_injective.comp (centralizer {δ}).subtype_injective))).trans
      (MulEquiv.subgroupCongr (centralizer_inl_delta hδ).symm)

/-- `hnnEquiv` sends `inr q` to `inl q`. -/
private theorem coe_hnnEquiv_inr (hδ : δ ≠ 1) (q : centralizer {δ})
    (hq : inr q ∈ centralizer {(inr (deltaQ δ) : G ∗ centralizer {δ})}) :
    (hnnEquiv hδ ⟨inr q, hq⟩ : G ∗ centralizer {δ}) = inl (q : G) := by
  -- In the range of `inr`, the element `inr q` is `inr.rangeRestrict q`.
  have h : MulEquiv.subgroupCongr (centralizer_inr_deltaQ hδ) ⟨inr q, hq⟩ =
      (inr : centralizer {δ} →* G ∗ centralizer {δ}).rangeRestrict q :=
    Subtype.ext (by simp)
  simp [hnnEquiv, h]

/-- After `baseHom`, the identification of the two copies of `C_G(δ)` is `x ↦ s⁻¹ x s`. -/
private theorem baseHom_hnnEquiv (hδ : δ ≠ 1)
    (a : centralizer {(inr (deltaQ δ) : G ∗ centralizer {δ})}) :
    baseHom ρ δ (hnnEquiv hδ a) = (t 0)⁻¹ * baseHom ρ δ a * t 0 := by
  obtain ⟨_, ha⟩ := a
  obtain ⟨q, rfl⟩ := (centralizer_inr_deltaQ hδ).le ha
  rw [coe_hnnEquiv_inr, Subgroup.coe_mk, baseHom_inl, baseHom_inr]
  group

/-- The homomorphism from `G[z]` to the HNN extension of `G ∗ C_G(δ)` along `hnnEquiv`, with
stable letter `t`, that is the inclusion on `G` and sends `z` to `t⁻¹`. -/
private noncomputable def toHNN (hδ : δ ≠ 1) :
    GX G Unit →* HNNExtension (G ∗ centralizer {δ}) _ _ (hnnEquiv hδ) :=
  (HNNExtension.map (.id _) (by rw [comap_id, centralizer_inr_deltaQ hδ])
    fun a => by
      obtain ⟨q, rfl⟩ := (inr : centralizer {δ} →* G ∗ centralizer {δ}).rangeRestrict_surjective a
      simp [coe_hnnEquiv_inr]).comp
      (HNNExtension.equivCoprodFreeGroup (centralizer {δ}).subtype_injective).symm.toMonoidHom

private theorem toHNN_injective (hδ : δ ≠ 1) : Function.Injective (toHNN hδ) :=
  (HNNExtension.map_injective Function.injective_id
    (by rw [comap_id, centralizer_inr_deltaQ hδ]) (by rw [comap_id, centralizer_inl_delta hδ])).comp
    (HNNExtension.equivCoprodFreeGroup _).symm.injective

end Injective

/-- Over the trivial group, `twoLetterHom ρ δ 0 0` is the homomorphism `ℤ → ℤ²`, `z ↦ (1, 1)`, which
is injective. -/
private theorem twoLetterHom_zero_injective_of_subsingleton [Subsingleton G] (ρ δ : G) :
    Function.Injective (twoLetterHom ρ δ (0 : Fin 1) (0 : Fin 1)) := by
  -- The homomorphism `G(ρ, s)(δ, u) →* ⟨z⟩` sending `u` to `z` and killing `G(ρ, s)` is a left
  -- inverse of `twoLetterHom` on `⟨z⟩`, which is all of `G[z]`.
  let ψ : CentralizerExt (of δ : CentralizerExt ρ 1) 1 →* FreeGroup Unit :=
    lift 1 (fun _ => FreeGroup.of ()) (fun _ _ => .refl _) fun _ _ _ => .one_left _
  have hψ : ψ.comp ((twoLetterHom ρ δ 0 0).comp inr) = .id _ :=
    FreeGroup.ext_hom _ _ fun _ => by simp [ψ]
  exact (Function.Injective.of_comp_iff' _ inr_bijective).1
    (Function.LeftInverse.injective (DFunLike.congr_fun hψ))

/-- The rank-one case of `twoLetterHom_injective_of_injective`. -/
private theorem twoLetterHom_zero_injective_of_injective {ρ δ : G}
    (hinj : Function.Injective (Monoid.Coprod.lift (centralizer {ρ}).subtype
      (centralizer {δ}).subtype)) :
    Function.Injective (twoLetterHom ρ δ (0 : Fin 1) (0 : Fin 1)) := by
  rcases eq_or_ne δ 1 with rfl | hδ
  · -- `C_G(ρ) ∗ G → G` is injective, so `C_G(ρ) = 1`; hence `ρ = 1` and `G = C_G(ρ)` is trivial.
    have h1 (g : G) (hg : g ∈ centralizer {ρ}) : g = 1 := by
      have h := @hinj (inl ⟨g, hg⟩) (inr ⟨g, mem_centralizer_singleton_iff.2 (.one_right g)⟩)
        (by simp)
      simpa using congrArg fst h
    have hρ := h1 ρ (mem_centralizer_singleton_iff.2 (.refl ρ))
    have : Subsingleton G := ⟨fun a b => by
      rw [h1 a (hρ ▸ mem_centralizer_singleton_iff.2 (.one_right a)),
        h1 b (hρ ▸ mem_centralizer_singleton_iff.2 (.one_right b))]⟩
    exact twoLetterHom_zero_injective_of_subsingleton ρ 1
  have hC : centralizer {baseHom ρ δ (inl δ)} = centralizer {(of δ : CentralizerExt ρ 1)} := by
    rw [baseHom_inl]
  -- `twoLetterHom` factors through the HNN extension of `G ∗ C_G(δ)`.
  have hsq : twoLetterHom ρ δ 0 0 = (CentralizerExt.congr hC).toMonoidHom.comp
      ((hnnLift (hnnEquiv hδ) (baseHom ρ δ) (t 0) (baseHom_hnnEquiv ρ hδ)).comp (toHNN hδ)) :=
    GX.ext_hom (fun g => by simp [toHNN, baseHom_inl]) fun _ => by simp [toHNN]
  rw [hsq, MonoidHom.coe_comp, MonoidHom.coe_comp]
  exact (CentralizerExt.congr hC).injective.comp <|
    (hnnLift_injective _ (coe_hnnEquiv_inr hδ _ _) (baseHom_injective ρ δ hinj) _).comp
      (toHNN_injective hδ)

/-- **The product of two new letters is free over the base.** If the centralizers of `ρ` and `δ`
generate their free product in `G`, the homomorphism `G[z] → G(ρ, s)(δ, u)`, `z ↦ sᵢ uⱼ`, is
injective. -/
theorem twoLetterHom_injective_of_injective {ρ δ : G}
    (hinj : Function.Injective (Monoid.Coprod.lift (centralizer {ρ}).subtype
      (centralizer {δ}).subtype)) (i : Fin m) (j : Fin n) :
    Function.Injective (twoLetterHom ρ δ i j) := by
  -- Keep the letters `sᵢ` and `uⱼ` and kill the others: `t k ↦ t 0 ^ [k = i]`, then `[k = j]`.
  let r₁ : CentralizerExt ρ m →* CentralizerExt ρ 1 :=
    lift of (fun k => t 0 ^ Pi.single (M := fun _ => ℤ) i 1 k) (fun _ _ => .zpow_zpow_self ..)
      fun _ hc _ => (commute_of_t hc 0).zpow_right _
  have hr₁ (c : CentralizerExt ρ m) (hc : c ∈ centralizer {of δ}) :
      r₁ c ∈ centralizer {(of δ : CentralizerExt ρ 1)} :=
    mem_centralizer_singleton_iff.2 <| by
      simpa [r₁] using (mem_centralizer_singleton_iff.1 hc).map r₁
  let r : CentralizerExt (of δ : CentralizerExt ρ m) n →*
      CentralizerExt (of δ : CentralizerExt ρ 1) 1 :=
    lift (of.comp r₁) (fun k => t 0 ^ Pi.single (M := fun _ => ℤ) j 1 k)
      (fun _ _ => .zpow_zpow_self ..) fun c hc _ => (commute_of_t (hr₁ c hc) 0).zpow_right _
  have hr : r.comp (twoLetterHom ρ δ i j) = twoLetterHom ρ δ 0 0 :=
    GX.ext_hom (fun g => by simp [r, r₁]) fun _ => by simp [r, r₁]
  refine Function.Injective.of_comp (f := r) ?_
  rw [← MonoidHom.coe_comp, hr]
  exact twoLetterHom_zero_injective_of_injective hinj

/-- **The product of two new letters is free over the base** ([VAR-I] Proposition 12). If `ρ` and
`δ` do not commute in the fully residually free group `G`, the homomorphism
`G[z] → G(ρ, s)(δ, u)`, `z ↦ sᵢ uⱼ`, is injective. -/
theorem twoLetterHom_injective (hG : IsFullyResiduallyFree G) {ρ δ : G} (h : ¬Commute ρ δ)
    (i : Fin m) (j : Fin n) : Function.Injective (twoLetterHom ρ δ i j) :=
  twoLetterHom_injective_of_injective (hG.coprodLift_subtype_centralizer_injective h) i j

/-- Let `F = F(a, b)` be the free group on `a` and `b`. Extend the centralizer of `a` in `F` by a
letter `s`, and then the centralizer of the image of `b` in `F(a, s)` by a letter `u`. The product
`s u` of the two new letters of `F(a, s)(b, u)` is free over `F`. -/
example : Function.Injective
    (twoLetterHom (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 1) (0 : Fin 1) (0 : Fin 1)) :=
  twoLetterHom_injective isFullyResiduallyFree_of_isFreeGroup
    (fun h => absurd (FreeGroup.eq_of_commute_of_of h) (by decide)) 0 0

end CentralizerExt

end TauCeti.LimitGroup
