/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Basic
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
import Mathlib.Tactic.Group
import TauCeti.GroupTheory.CoprodI.Centralizer
import TauCeti.GroupTheory.HNNExtension.Double
import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.HNN
import TauCeti.GroupTheory.LimitGroup.TwoGenerator
import TauCeti.GroupTheory.PushoutI.Map

/-!
# A free letter in two extensions of centralizers

Let `G` be a fully residually free group and `ρ`, `δ` two elements of `G` that do not commute.
Extend the centralizer of `ρ` by a letter `s`, and then the centralizer of `δ` in `G(ρ, s)` by a
letter `u`. The product `s u` is free over `G`: the homomorphism `G[z] → G(ρ, s)(δ, u)` sending
the variable `z` to `s u` is injective (`CentralizerExt.twoLetterHom_injective`). Conjugation by
`s u` therefore embeds a second copy of `G`, and it turns `ρ` into `u⁻¹ ρ u`; this is the device
by which Kharlampovich and Myasnikov replace, one atom at a time, a solution of a quadratic
equation by a generic one.

The second letter extends the full centralizer of `δ` in `G(ρ, s)`, as an extension of a
centralizer of that group must. It is larger than `C_G(δ)` when `δ` is conjugate into `C_G(ρ)`; in
[VAR-I] the second letter extends `C_G(δ)` and that case is excluded by an assumption on the
conjugates of `C_G(δ)`, which is not needed here. The only input from full residual freeness is
that the centralizers of `ρ` and `δ` generate their free product
(`IsFullyResiduallyFree.coprodLift_subtype_centralizer_injective`, [VAR-I] Lemma 21).

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt.twoLetterHom ρ δ`: the homomorphism
  `G[z] →* G(ρ, s)(δ, u)` over `G` sending `z` to `s u`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.twoLetterHom_conj`: conjugation by `s u` sends `ρ` to
  `u⁻¹ ρ u`.
* `TauCeti.LimitGroup.CentralizerExt.twoLetterHom_injective`: if `ρ` and `δ` do not commute in the
  fully residually free group `G`, the homomorphism `twoLetterHom ρ δ` is injective.

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

variable {G : Type u} [Group G]

/-- The new letters of an extension of the centralizer of `u` commute with `u`. -/
theorem commute_of_self_t {u : G} {n : ℕ} (i : Fin n) :
    Commute (of u : CentralizerExt u n) (t i) :=
  commute_of_t (mem_centralizer_singleton_iff.2 (.refl u)) i

/-- The homomorphism `G[z] → G(ρ, s)(δ, u)` over `G` sending the variable `z` to `s u`, where `s`
is the new letter of the extension `G(ρ, s)` of the centralizer of `ρ` and `u` the new letter of
the extension of the centralizer of `δ` in `G(ρ, s)`. -/
def twoLetterHom (ρ δ : G) :
    GX G Unit →* CentralizerExt (of δ : CentralizerExt ρ 1) 1 :=
  eval (of.comp of) fun _ => of (t 0) * t 0

@[simp]
theorem twoLetterHom_inl (ρ δ g : G) : twoLetterHom ρ δ (inl g) = of (of g) := by
  simp [twoLetterHom]

@[simp]
theorem twoLetterHom_inr_of (ρ δ : G) (x : Unit) :
    twoLetterHom ρ δ (inr (FreeGroup.of x)) = of (t 0) * t 0 := by
  simp [twoLetterHom]

/-- Conjugation by `s u` carries `ρ` to `u⁻¹ ρ u`: the letter `s` commutes with `ρ`. -/
theorem twoLetterHom_conj (ρ δ : G) :
    twoLetterHom ρ δ ((inr (FreeGroup.of ()))⁻¹ * inl ρ * inr (FreeGroup.of ())) =
      (t 0)⁻¹ * of (of ρ) * t 0 := by
  have hc : Commute (of (of ρ) : CentralizerExt (of δ : CentralizerExt ρ 1) 1) (of (t 0)) :=
    (commute_of_self_t 0).map of
  simp only [map_mul, map_inv, twoLetterHom_inl, twoLetterHom_inr_of]
  calc (of (t 0) * t 0)⁻¹ * of (of ρ) * (of (t 0) * t 0)
      = (t 0)⁻¹ * ((of (t 0))⁻¹ * (of (of ρ) * of (t 0))) * t 0 := by group
    _ = (t 0)⁻¹ * of (of ρ) * t 0 := by rw [hc.eq, inv_mul_cancel_left]

/-! ### Injectivity

Write `C = C_G(ρ)`, `Q = C_G(δ)` and `K = G(ρ, s)`. In the free product `G ∗ Q` the centralizer of
`δ` in the free factor `Q` is that factor, and the centralizer of `δ ∈ G` is the copy of `Q` in `G`
(`Monoid.CoprodI.centralizer_of_eq_map`). The group `G[z]` embeds in the HNN extension of `G ∗ Q`
along the identification of the two, `t q t⁻¹ = q`, by the inclusion on `G` and `z ↦ t⁻¹`; a left
inverse is the inclusion on `G`, `q ↦ z q z⁻¹` on the free factor and `t ↦ z⁻¹`. The homomorphism
`θ : G ∗ Q →* K` that is the inclusion on `G` and `q ↦ s q s⁻¹` on the free factor is injective
because `C` and `Q` generate their free product in `G` (Lemma 21): `G ∗ Q` is the amalgam
`G ∗_C (C ∗ Q)`, which embeds in the double `G ∗_C G`, and the double embeds in `K`. After `θ`,
the identification of the two copies of `Q` is conjugation by `s`, so the HNN extension embeds in
`K(θ δ, ℤ) = K(δ, ℤ)` by `θ` and `t ↦ (s u)⁻¹` (`CentralizerExt.hnnLift_injective`). The composite
is `twoLetterHom ρ δ`. -/

section Injective

variable (ρ δ : G)

/-- The factors `G` and `C_G(δ)` of the free product `G ∗ C_G(δ)`. -/
private abbrev QFactor (b : Bool) : Type u :=
  cond b (centralizer {δ}) G

private instance (b : Bool) : Group (QFactor δ b) :=
  Bool.rec (motive := fun b => Group (QFactor δ b)) (inferInstanceAs (Group G))
    (inferInstanceAs (Group (centralizer {δ}))) b

/-- The factors `G` and `C_G(ρ) ∗ C_G(δ)` of the amalgam `G ∗_{C_G(ρ)} (C_G(ρ) ∗ C_G(δ))`. -/
private abbrev AmalgFactor (b : Bool) : Type u :=
  cond b (Monoid.Coprod (centralizer {ρ}) (centralizer {δ})) G

private instance (b : Bool) : Group (AmalgFactor ρ δ b) :=
  Bool.rec (motive := fun b => Group (AmalgFactor ρ δ b)) (inferInstanceAs (Group G))
    (inferInstanceAs (Group (Monoid.Coprod (centralizer {ρ}) (centralizer {δ})))) b

/-- The two embeddings of `C_G(ρ)` amalgamated in `G ∗_{C_G(ρ)} (C_G(ρ) ∗ C_G(δ))`. -/
private def amalgMap : ∀ b, centralizer {ρ} →* AmalgFactor ρ δ b
  | false => (centralizer {ρ}).subtype
  | true => Monoid.Coprod.inl

/-- The isomorphism `G ∗ C_G(δ) → G ∗_{C_G(ρ)} (C_G(ρ) ∗ C_G(δ))`, as a homomorphism. -/
private def toAmalg : Monoid.CoprodI (QFactor δ) →* Monoid.PushoutI (amalgMap ρ δ) :=
  Monoid.CoprodI.lift (Bool.rec (motive := fun b => QFactor δ b →* _)
    (Monoid.PushoutI.of (φ := amalgMap ρ δ) false)
    ((Monoid.PushoutI.of (φ := amalgMap ρ δ) true).comp Monoid.Coprod.inr))

/-- The inverse of `toAmalg`. -/
private def ofAmalg : Monoid.PushoutI (amalgMap ρ δ) →* Monoid.CoprodI (QFactor δ) :=
  Monoid.PushoutI.lift (Bool.rec (motive := fun b => AmalgFactor ρ δ b →* _)
      (Monoid.CoprodI.of (M := QFactor δ) (i := false))
      (Monoid.Coprod.lift ((Monoid.CoprodI.of (M := QFactor δ) (i := false)).comp
        (centralizer {ρ}).subtype) (Monoid.CoprodI.of (M := QFactor δ) (i := true))))
    ((Monoid.CoprodI.of (M := QFactor δ) (i := false)).comp (centralizer {ρ}).subtype)
    fun b => by cases b <;> rfl

private theorem toAmalg_injective : Function.Injective (toAmalg ρ δ) := by
  refine Function.LeftInverse.injective (g := ofAmalg ρ δ) fun x => ?_
  rw [← MonoidHom.comp_apply]
  refine DFunLike.congr_fun (Monoid.CoprodI.ext_hom _ (.id _) fun b => ?_) x
  cases b
  · ext
    simp [toAmalg, ofAmalg]
  · ext
    simp only [toAmalg, ofAmalg, MonoidHom.coe_comp, Function.comp_apply,
      Monoid.CoprodI.lift_of, Monoid.PushoutI.lift_of, MonoidHom.id_apply]
    -- The instances on the `Bool`-indexed factors hide `Monoid.Coprod.lift_apply_inr` from `simp`.
    rfl

/-- The homomorphism `G ∗_{C_G(ρ)} (C_G(ρ) ∗ C_G(δ)) → G ∗_{C_G(ρ)} G` induced by the inclusions
of `C_G(ρ)` and `C_G(δ)` in the second copy of `G`. -/
private def amalgToDouble :
    Monoid.PushoutI (amalgMap ρ δ) →* Monoid.PushoutI fun _ : Bool => (centralizer {ρ}).subtype :=
  Monoid.PushoutI.map (Bool.rec (motive := fun b => AmalgFactor ρ δ b →* G) (.id G)
    (Monoid.Coprod.lift (centralizer {ρ}).subtype (centralizer {δ}).subtype)) (.id _)
    fun b => by cases b <;> rfl

private theorem amalgToDouble_injective (hG : IsFullyResiduallyFree G) (h : ¬Commute ρ δ) :
    Function.Injective (amalgToDouble ρ δ) := by
  refine Monoid.PushoutI.map_injective _ (fun _ => Subtype.val_injective) Function.injective_id
    fun b g hg => ?_
  cases b
  · exact hg
  · -- An element of `C_G(ρ) ∗ C_G(δ)` mapped into `C_G(ρ)` lies in the first factor, by Lemma 21.
    obtain ⟨c, hc⟩ := hg
    exact ⟨c, hG.coprodLift_subtype_centralizer_injective h hc⟩

/-- The homomorphism `G ∗ C_G(δ) →* G(ρ, s)` that is the inclusion on `G` and `q ↦ s q s⁻¹` on
`C_G(δ)`. -/
private def baseHom : Monoid.CoprodI (QFactor δ) →* CentralizerExt ρ 1 :=
  (equivHNNExtension (u := ρ)).symm.toMonoidHom.comp
    ((HNNExtension.ofDouble _).comp ((amalgToDouble ρ δ).comp (toAmalg ρ δ)))

private theorem baseHom_of_false (g : G) :
    baseHom ρ δ (Monoid.CoprodI.of (M := QFactor δ) (i := false) g) = of g := by
  simp only [baseHom, MulEquiv.toMonoidHom_eq_coe, amalgToDouble, toAmalg, MonoidHom.coe_comp,
    MonoidHom.coe_ofClass, Function.comp_apply, Monoid.CoprodI.lift_of, Monoid.PushoutI.map_of,
    HNNExtension.ofDouble_of_false, equivHNNExtension_symm_of, of_inj]
  -- The factor homomorphism `Bool.rec (.id G) _ false` is the identity only up to unfolding.
  rfl

private theorem baseHom_of_true (q : centralizer {δ}) :
    baseHom ρ δ (Monoid.CoprodI.of (M := QFactor δ) (i := true) q) =
      t 0 * of (q : G) * (t 0)⁻¹ := by
  simp only [baseHom, MulEquiv.toMonoidHom_eq_coe, amalgToDouble, toAmalg, MonoidHom.coe_comp,
    MonoidHom.coe_ofClass, Function.comp_apply, Monoid.CoprodI.lift_of, Monoid.PushoutI.map_of,
    HNNExtension.ofDouble_of_true, map_mul, equivHNNExtension_symm_t, equivHNNExtension_symm_of,
    map_inv, mul_left_inj, mul_right_inj, of_inj]
  -- `Monoid.Coprod.lift _ _ (inr q)` reduces to `q` only up to unfolding.
  rfl

private theorem baseHom_injective (hG : IsFullyResiduallyFree G) (h : ¬Commute ρ δ) :
    Function.Injective (baseHom ρ δ) :=
  (equivHNNExtension (u := ρ)).symm.injective.comp <| (HNNExtension.ofDouble_injective _).comp <|
    (amalgToDouble_injective ρ δ hG h).comp (toAmalg_injective ρ δ)

/-- The element `δ` of the factor `G` of `G ∗ C_G(δ)`. -/
private abbrev deltaG : Monoid.CoprodI (QFactor δ) :=
  Monoid.CoprodI.of (M := QFactor δ) (i := false) δ

/-- The element `δ` of the free factor `C_G(δ)` of `G ∗ C_G(δ)`. -/
private abbrev deltaQ : Monoid.CoprodI (QFactor δ) :=
  Monoid.CoprodI.of (M := QFactor δ) (i := true) ⟨δ, mem_centralizer_singleton_iff.2 (.refl δ)⟩

variable {δ}

/-- The centralizer of `δ ∈ G` in `G ∗ C_G(δ)` is the copy of `C_G(δ)` in `G`. -/
private theorem centralizer_deltaG (hδ : δ ≠ 1) :
    centralizer {deltaG δ} =
      (centralizer {δ}).map (Monoid.CoprodI.of (M := QFactor δ) (i := false)) :=
  Monoid.CoprodI.centralizer_of_eq_map hδ

/-- The centralizer of `δ ∈ C_G(δ)` in `G ∗ C_G(δ)` is the free factor `C_G(δ)`. -/
private theorem centralizer_deltaQ (hδ : δ ≠ 1) :
    centralizer {deltaQ δ} = (Monoid.CoprodI.of (M := QFactor δ) (i := true)).range := by
  rw [Monoid.CoprodI.centralizer_of_eq_map (G := QFactor δ) (i := true)
    (g := ⟨δ, mem_centralizer_singleton_iff.2 (.refl δ)⟩) fun h => hδ (congrArg Subtype.val h),
    MonoidHom.range_eq_map]
  -- Every element of `C_G(δ)` commutes with `δ`.
  exact congrArg _ <| eq_top_iff.2 fun (q : centralizer {δ}) _ =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 q.property))

/-- The identification of the centralizer of `δ ∈ C_G(δ)` in `G ∗ C_G(δ)`, the free factor
`C_G(δ)`, with the centralizer of `δ ∈ G`, the copy of `C_G(δ)` in `G`. -/
private noncomputable def hnnEquiv (hδ : δ ≠ 1) :
    centralizer {deltaQ δ} ≃* centralizer {deltaG δ} :=
  (MulEquiv.subgroupCongr (centralizer_deltaQ hδ)).trans <|
    (MonoidHom.ofInjective (Monoid.CoprodI.of_injective (M := QFactor δ) true)).symm.trans <|
      ((centralizer {δ}).equivMapOfInjective _
        (Monoid.CoprodI.of_injective (M := QFactor δ) false)).trans
        (MulEquiv.subgroupCongr (centralizer_deltaG hδ).symm)

/-- An element of the centralizer of `δ ∈ C_G(δ)` in `G ∗ C_G(δ)` is some `q ∈ C_G(δ)` in the free
factor, and `hnnEquiv` sends it to `q` in the factor `G`. -/
private theorem exists_hnnEquiv_eq (hδ : δ ≠ 1) (a : centralizer {deltaQ δ}) :
    ∃ q : centralizer {δ},
      (a : Monoid.CoprodI (QFactor δ)) = Monoid.CoprodI.of (M := QFactor δ) (i := true) q ∧
        (hnnEquiv hδ a : Monoid.CoprodI (QFactor δ)) =
          Monoid.CoprodI.of (M := QFactor δ) (i := false) (q : G) :=
  let a' : (Monoid.CoprodI.of (M := QFactor δ) (i := true)).range :=
    ⟨a, centralizer_deltaQ hδ ▸ a.property⟩
  ⟨(MonoidHom.ofInjective (Monoid.CoprodI.of_injective (M := QFactor δ) true)).symm a',
    (MonoidHom.apply_ofInjective_symm (Monoid.CoprodI.of_injective (M := QFactor δ) true) a').symm,
    rfl⟩

private theorem hnnEquiv_deltaQ (hδ : δ ≠ 1) :
    (hnnEquiv hδ ⟨deltaQ δ, mem_centralizer_singleton_iff.2 (.refl _)⟩ :
      Monoid.CoprodI (QFactor δ)) = deltaG δ := by
  obtain ⟨q, ha, hb⟩ := exists_hnnEquiv_eq hδ ⟨deltaQ δ, mem_centralizer_singleton_iff.2 (.refl _)⟩
  rw [hb, ← (Monoid.CoprodI.of_injective (M := QFactor δ) true) ha]

/-- After `baseHom`, the identification of the two copies of `C_G(δ)` is conjugation by `s`. -/
private theorem baseHom_hnnEquiv (hδ : δ ≠ 1) (a : centralizer {deltaQ δ}) :
    baseHom ρ δ (hnnEquiv hδ a) = (t 0)⁻¹ * baseHom ρ δ a * t 0 := by
  obtain ⟨q, ha, hb⟩ := exists_hnnEquiv_eq hδ a
  rw [ha, hb, baseHom_of_true, baseHom_of_false]
  group

/-- The homomorphism from `G[z]` to the HNN extension of `G ∗ C_G(δ)` along `hnnEquiv`, with
stable letter `t`, that is the inclusion on `G` and sends `z` to `t⁻¹`. -/
private noncomputable def toHNN (hδ : δ ≠ 1) :
    GX G Unit →* HNNExtension (Monoid.CoprodI (QFactor δ)) _ _ (hnnEquiv hδ) :=
  eval (HNNExtension.of.comp (Monoid.CoprodI.of (M := QFactor δ) (i := false)))
    fun _ => HNNExtension.t⁻¹

/-- The left inverse of `toHNN`: the inclusion on `G`, `q ↦ z q z⁻¹` on `C_G(δ)`, `t ↦ z⁻¹`. -/
private noncomputable def ofHNN (hδ : δ ≠ 1) :
    HNNExtension (Monoid.CoprodI (QFactor δ)) _ _ (hnnEquiv hδ) →* GX G Unit :=
  HNNExtension.lift
    (Monoid.CoprodI.lift (Bool.rec (motive := fun b => QFactor δ b →* GX G Unit) inl
      ((MulAut.conj (inr (FreeGroup.of ()))).toMonoidHom.comp
        (inl.comp (centralizer {δ}).subtype))))
    (inr (FreeGroup.of ()))⁻¹ fun a => by
      obtain ⟨q, ha, hb⟩ := exists_hnnEquiv_eq hδ a
      rw [ha, hb]
      simp only [MulEquiv.toMonoidHom_eq_coe, Monoid.CoprodI.lift_of, MonoidHom.coe_comp,
        MonoidHom.coe_ofClass, Function.comp_apply, MulAut.conj_apply, mul_assoc,
        inv_mul_cancel_left]
      -- `(centralizer {δ}).subtype q` is `q` up to unfolding.
      rfl

private theorem toHNN_injective (hδ : δ ≠ 1) : Function.Injective (toHNN hδ) := by
  refine Function.LeftInverse.injective (g := ofHNN hδ) fun x => ?_
  rw [← MonoidHom.comp_apply]
  exact DFunLike.congr_fun (GX.ext_hom (φ := (ofHNN hδ).comp (toHNN hδ)) (ψ := .id _)
    (fun g => by simp [ofHNN, toHNN]) fun _ => by simp [ofHNN, toHNN]) x

end Injective

/-- **The product of the two new letters is free over the base.** If `ρ` and `δ` do not commute
in the fully residually free group `G`, the homomorphism `G[z] → G(ρ, s)(δ, u)`, `z ↦ s u`, is
injective. -/
theorem twoLetterHom_injective (hG : IsFullyResiduallyFree G) {ρ δ : G} (h : ¬Commute ρ δ) :
    Function.Injective (twoLetterHom ρ δ) := by
  have hδ : δ ≠ 1 := by
    rintro rfl
    exact h (.one_right ρ)
  have hC : centralizer {baseHom ρ δ (deltaG δ)} = centralizer {(of δ : CentralizerExt ρ 1)} := by
    rw [baseHom_of_false]
  -- `twoLetterHom` factors through the HNN extension of `G ∗ C_G(δ)`.
  have hsq : twoLetterHom ρ δ = (CentralizerExt.congr hC).toMonoidHom.comp
      ((hnnLift (hnnEquiv hδ) (baseHom ρ δ) (t 0) (baseHom_hnnEquiv ρ hδ)).comp (toHNN hδ)) :=
    GX.ext_hom (fun g => by simp [toHNN, -of_inj, baseHom_of_false ρ δ g]) fun _ => by
      simp [toHNN]
  rw [hsq, MonoidHom.coe_comp, MonoidHom.coe_comp]
  exact (CentralizerExt.congr hC).injective.comp <|
    (hnnLift_injective _ (hnnEquiv_deltaQ hδ) (baseHom_injective ρ δ hG h) _).comp
      (toHNN_injective hδ)

/-- Over the free group `F(a, b)`, the product `s u` of the new letters of `F(a, s)(b, u)` is free
over `F(a, b)`. -/
example : Function.Injective (twoLetterHom (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 1)) :=
  twoLetterHom_injective isFullyResiduallyFree_of_isFreeGroup fun h =>
    absurd (FreeGroup.eq_of_commute_of_of h) (by decide)

end CentralizerExt

end TauCeti.LimitGroup
