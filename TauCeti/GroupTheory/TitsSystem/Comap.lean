/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Bruhat.Basic
import Mathlib.Tactic.Group

/-!
# Pulling a Tits system back along a homomorphism

Let `(B, N)` be a Tits system in `G` and write `T = B ∩ N`. If `f : H →* G` is a group
homomorphism with `G = f(H) T`, that is, every element of `G` is `f x * t` for some `x : H` and
some `t ∈ B ∩ N`, then the preimages `f⁻¹(B)` and `f⁻¹(N)` form a Tits system in `H`. Its Weyl
group is canonically the Weyl group of `(B, N)`, and its simple reflections are the preimages of
the simple reflections of `(B, N)`.

The main example is a normal subgroup `H` of `G` with `G = H T`, such as the special linear group
inside the general linear group, where the diagonal torus supplies the missing determinants. The
homomorphism need not be injective: pulling back along a surjection also gives a Tits system.

The key step is that Bruhat cells pull back to Bruhat cells: for `w : H` with `f w ∈ N`, the
preimage of `B f(w) B` is the double coset `f⁻¹(B) w f⁻¹(B)`
(`TauCeti.TitsSystem.preimage_doubleCoset`). This is where the hypothesis `G = f(H) T` enters:
it lets the factors from `B` be replaced by factors from `f⁻¹(B)`, with the leftover element of
`T` moved past `f w`, which normalizes `T`.

## Main declarations

* `TauCeti.TitsSystem.preimage_doubleCoset`: the preimage of a Bruhat cell is a Bruhat cell.
* `TauCeti.TitsSystem.comap`: the Tits system `(f⁻¹(B), f⁻¹(N))` in `H`.
* `TauCeti.TitsSystem.comapWeylGroupMulEquiv`: its Weyl group is the Weyl group of `(B, N)`.
* `TauCeti.TitsSystem.comap_simple`: its simple reflections correspond to those of `(B, N)`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter IV, §2.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 29.1.
-/

public section

namespace TauCeti.TitsSystem

universe u v

variable {G : Type u} [Group G] (T : TitsSystem G) {H : Type v} [Group H] (f : H →* G)

/-- Conjugation by an element of `N` preserves `B ∩ N`, read in `G`. -/
private theorem conj_mem_subgroupB {n t : G} (hn : n ∈ T.subgroupN)
    (ht : t ∈ T.subgroupB ⊓ T.subgroupN) : n * t * n⁻¹ ∈ T.subgroupB :=
  Subgroup.mem_subgroupOf.mp (T.intersection_normal.conj_mem ⟨t, ht.2⟩ ht.1 ⟨n, hn⟩)

variable {f}

/-- **Bruhat cells pull back to Bruhat cells.** If `G = f(H) (B ∩ N)`, then for every `w : H`
with `f w ∈ N`, the preimage of the double coset `B f(w) B` is the double coset
`f⁻¹(B) w f⁻¹(B)`. -/
theorem preimage_doubleCoset
    (hf : ∀ g : G, ∃ x : H, ∃ t ∈ T.subgroupB ⊓ T.subgroupN, f x * t = g)
    {w : H} (hw : f w ∈ T.subgroupN) :
    f ⁻¹' DoubleCoset.doubleCoset (f w) T.subgroupB T.subgroupB =
      DoubleCoset.doubleCoset w (T.subgroupB.comap f) (T.subgroupB.comap f) := by
  ext z
  simp only [Set.mem_preimage, DoubleCoset.mem_doubleCoset, SetLike.mem_coe,
    Subgroup.mem_comap]
  constructor
  · rintro ⟨b, hb, b', hb', hz⟩
    obtain ⟨x, t, ht, rfl⟩ := hf b
    have hx : f x ∈ T.subgroupB := by
      simpa using mul_mem hb (inv_mem ht.1)
    -- The factor `t ∈ B ∩ N` moves to the right past `f w`, which normalizes `B ∩ N`.
    have hconj := T.conj_mem_subgroupB (inv_mem hw) ht
    refine ⟨x, hx, w⁻¹ * x⁻¹ * z, ?_, by group⟩
    have hfz : f (w⁻¹ * x⁻¹ * z) = (f w)⁻¹ * t * (f w)⁻¹⁻¹ * b' := by
      rw [map_mul, map_mul, map_inv, map_inv, hz]
      group
    rw [hfz]
    exact mul_mem hconj hb'
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨f x, hx, f y, hy, by rw [map_mul, map_mul]⟩

/-- An element of `N` differs from the image of an element of `f⁻¹(N)` by an element of
`B ∩ N`. -/
private theorem exists_mem_subgroupN_mul_eq
    (hf : ∀ g : G, ∃ x : H, ∃ t ∈ T.subgroupB ⊓ T.subgroupN, f x * t = g)
    {n : G} (hn : n ∈ T.subgroupN) :
    ∃ x : H, f x ∈ T.subgroupN ∧ ∃ t ∈ T.subgroupB ⊓ T.subgroupN, f x * t = n := by
  obtain ⟨x, t, ht, hxt⟩ := hf n
  refine ⟨x, ?_, t, ht, hxt⟩
  rw [eq_mul_inv_of_mul_eq hxt]
  exact mul_mem hn (inv_mem ht.2)

/-- The intersection `f⁻¹(B) ∩ f⁻¹(N)`, read inside `f⁻¹(N)`, is the preimage of `B ∩ N`. -/
private theorem comap_subgroupOf_eq :
    (T.subgroupB.comap f).subgroupOf (T.subgroupN.comap f) =
      T.intersection.comap (f.subgroupComap T.subgroupN) := by
  ext n
  exact Iff.rfl

private instance :
    ((T.subgroupB.comap f).subgroupOf (T.subgroupN.comap f)).Normal := by
  rw [comap_subgroupOf_eq]
  exact Subgroup.Normal.comap inferInstance _

/-- `MonoidHom.subgroupComap_apply_coe` restated for a subgroup-typed argument, so that it
can be used for rewriting. -/
private theorem coe_subgroupComap (n : T.subgroupN.comap f) :
    ((f.subgroupComap T.subgroupN n : T.subgroupN) : G) = f n :=
  f.subgroupComap_apply_coe T.subgroupN n

/-- The homomorphism of Weyl groups induced by `f`. -/
private def comapWeylGroupHom :
    T.subgroupN.comap f ⧸ (T.subgroupB.comap f).subgroupOf (T.subgroupN.comap f) →*
      T.WeylGroup :=
  QuotientGroup.map _ _ (f.subgroupComap T.subgroupN) (comap_subgroupOf_eq T).le

private theorem comapWeylGroupHom_mk (n : T.subgroupN.comap f) :
    comapWeylGroupHom T (QuotientGroup.mk n) = QuotientGroup.mk (f.subgroupComap T.subgroupN n) :=
  QuotientGroup.map_mk _ _ _ _ _

private theorem comapWeylGroupHom_injective :
    Function.Injective (comapWeylGroupHom T (f := f)) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H n =>
    rw [comapWeylGroupHom_mk, QuotientGroup.eq_one_iff] at hq
    exact (QuotientGroup.eq_one_iff n).mpr hq

private theorem comapWeylGroupHom_surjective
    (hf : ∀ g : G, ∃ x : H, ∃ t ∈ T.subgroupB ⊓ T.subgroupN, f x * t = g) :
    Function.Surjective (comapWeylGroupHom T (f := f)) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H n =>
    obtain ⟨x, hx, t, ht, hxt⟩ := T.exists_mem_subgroupN_mul_eq hf n.2
    refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
    rw [comapWeylGroupHom_mk, QuotientGroup.eq, mem_intersection]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_subgroupComap, ← hxt, inv_mul_cancel_left]
    exact ht.1

private theorem closure_preimage_comapWeylGroupHom
    (hf : ∀ g : G, ∃ x : H, ∃ t ∈ T.subgroupB ⊓ T.subgroupN, f x * t = g) :
    Subgroup.closure (comapWeylGroupHom T (f := f) ⁻¹' T.simple) = ⊤ := by
  let e := MulEquiv.ofBijective (comapWeylGroupHom T (f := f))
    ⟨comapWeylGroupHom_injective T, comapWeylGroupHom_surjective T hf⟩
  have he : comapWeylGroupHom T (f := f) ⁻¹' T.simple = e.symm '' T.simple :=
    (e.image_symm_eq_preimage T.simple).symm
  rw [he, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure, T.closure_simple]
  exact Subgroup.map_top_of_surjective _ e.symm.surjective

variable (f)

/-- The **pullback of a Tits system** along a homomorphism `f : H →* G` with `G = f(H) (B ∩ N)`:
the subgroups `f⁻¹(B)` and `f⁻¹(N)` of `H`, with the simple reflections corresponding to those of
`(B, N)` under the identification of Weyl groups `TauCeti.TitsSystem.comapWeylGroupMulEquiv`. -/
def comap (hf : ∀ g : G, ∃ x : H, ∃ t ∈ T.subgroupB ⊓ T.subgroupN, f x * t = g) :
    TitsSystem H where
  subgroupB := T.subgroupB.comap f
  subgroupN := T.subgroupN.comap f
  closure_subgroupB_union_subgroupN := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨n, hn⟩ := T.exists_mem_doubleCoset (f z)
    obtain ⟨x, hx, t, ht, hxt⟩ := T.exists_mem_subgroupN_mul_eq hf n.2
    have hcell : DoubleCoset.doubleCoset (n : G) T.subgroupB T.subgroupB =
        DoubleCoset.doubleCoset (f x) T.subgroupB T.subgroupB :=
      DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.mpr
        ⟨1, one_mem _, t, ht.1, by rw [one_mul, hxt]⟩)
    rw [hcell, ← Set.mem_preimage, T.preimage_doubleCoset hf hx,
      DoubleCoset.mem_doubleCoset] at hn
    obtain ⟨b, hb, b', hb', rfl⟩ := hn
    exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl hb))
      (Subgroup.subset_closure (Or.inr hx))) (Subgroup.subset_closure (Or.inl hb'))
  intersection_normal := inferInstance
  simple := comapWeylGroupHom T ⁻¹' T.simple
  closure_simple := closure_preimage_comapWeylGroupHom T hf
  exists_simpleRep_sq_mem s hs := by
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨r, rfl, ?_⟩
    -- The square of the class of `r` maps to the square of a simple reflection, which is `1`.
    have hsq : comapWeylGroupHom T (QuotientGroup.mk (r * r)) = 1 := by
      rw [QuotientGroup.mk_mul, map_mul]
      exact T.simple_sq_eq_one hs
    exact (QuotientGroup.eq_one_iff _).mp
      ((injective_iff_map_eq_one _).mp (comapWeylGroupHom_injective T) _ hsq)
  mul_doubleCoset_subset s hs := by
    obtain ⟨r₀, hr₀, hmul⟩ := T.mul_doubleCoset_subset _ hs
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨r, rfl, fun w ↦ ?_⟩
    have hr : f r ∈ T.subgroupN := r.2
    have hw : f w ∈ T.subgroupN := w.2
    -- `r₀ = f r * t` for some `t ∈ B ∩ N`.
    rw [comapWeylGroupHom_mk, eq_comm, QuotientGroup.eq, mem_intersection, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_subgroupComap] at hr₀
    set t : G := (f r)⁻¹ * r₀ with ht_def
    have ht : t ∈ T.subgroupB ⊓ T.subgroupN :=
      Subgroup.mem_inf.mpr ⟨hr₀, mul_mem (inv_mem hr) r₀.2⟩
    have hr₀t : (r₀ : G) = f r * t := by rw [ht_def, mul_inv_cancel_left]
    have hcell_r : DoubleCoset.doubleCoset (f r) T.subgroupB T.subgroupB =
        DoubleCoset.doubleCoset (r₀ : G) T.subgroupB T.subgroupB :=
      (DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.mpr
        ⟨1, one_mem _, t, ht.1, by rw [one_mul, hr₀t]⟩)).symm
    have hcell_rw : DoubleCoset.doubleCoset ((r₀ * f.subgroupComap T.subgroupN w : _) : G)
        T.subgroupB T.subgroupB = DoubleCoset.doubleCoset (f (r * w)) T.subgroupB T.subgroupB := by
      refine DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.mpr
        ⟨1, one_mem _, (f w)⁻¹ * t * (f w)⁻¹⁻¹, T.conj_mem_subgroupB (inv_mem hw) ht, ?_⟩)
      simp only [Subgroup.coe_mul, coe_subgroupComap, hr₀t, map_mul]
      group
    intro z hz
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_mul.mp hz
    have hrw : f (r * w) ∈ T.subgroupN := by
      rw [map_mul]
      exact mul_mem hr hw
    rw [← T.preimage_doubleCoset hf hr] at hz₁
    rw [← T.preimage_doubleCoset hf hw] at hz₂
    have hmem := hmul (f.subgroupComap T.subgroupN w)
      (Set.mul_mem_mul (hcell_r ▸ hz₁) hz₂)
    rw [hcell_rw] at hmem
    rw [Subgroup.coe_mul, ← T.preimage_doubleCoset hf hrw, ← T.preimage_doubleCoset hf hw]
    simpa only [Set.mem_union, Set.mem_preimage, map_mul, coe_subgroupComap] using hmem
  exists_conj_not_mem s hs := by
    obtain ⟨r₀, hr₀, b, hb⟩ := T.exists_conj_not_mem _ hs
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
    have hr : f r ∈ T.subgroupN := r.2
    rw [comapWeylGroupHom_mk, eq_comm, QuotientGroup.eq, mem_intersection, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_subgroupComap] at hr₀
    set t : G := (f r)⁻¹ * r₀ with ht_def
    have ht : t ∈ T.subgroupB ⊓ T.subgroupN :=
      Subgroup.mem_inf.mpr ⟨hr₀, mul_mem (inv_mem hr) r₀.2⟩
    have hr₀t : (r₀ : G) = f r * t := by rw [ht_def, mul_inv_cancel_left]
    -- Write `t b t⁻¹ = f x * t₁` with `f x ∈ B` and `t₁ ∈ B ∩ N`.
    obtain ⟨x, t₁, ht₁, hxt₁⟩ := hf (t * b * t⁻¹)
    have hx : f x ∈ T.subgroupB := by
      rw [eq_mul_inv_of_mul_eq hxt₁]
      exact mul_mem (mul_mem (mul_mem ht.1 b.2) (inv_mem ht.1)) (inv_mem ht₁.1)
    refine ⟨r, rfl, ⟨x, hx⟩, fun hmem ↦ hb ?_⟩
    -- Then `r₀ b r₀⁻¹ = f (r x r⁻¹) * (f r) t₁ (f r)⁻¹`, and both factors lie in `B`.
    have hconj : (r₀ : G) * b * (r₀ : G)⁻¹ =
        f ((r : H) * x * (r : H)⁻¹) * (f r * t₁ * (f r)⁻¹) := by
      rw [hr₀t, map_mul, map_mul, map_inv]
      calc f r * t * b * (f r * t)⁻¹ = f r * (t * b * t⁻¹) * (f r)⁻¹ := by group
        _ = f r * (f x * t₁) * (f r)⁻¹ := by rw [hxt₁]
        _ = _ := by group
    rw [hconj]
    exact mul_mem hmem (T.conj_mem_subgroupB hr ht₁)

variable (hf : ∀ g : G, ∃ x : H, ∃ t ∈ T.subgroupB ⊓ T.subgroupN, f x * t = g)

/-- The `B` subgroup of the pulled-back Tits system is the preimage of `B`. -/
@[simp]
theorem comap_subgroupB : (T.comap f hf).subgroupB = T.subgroupB.comap f :=
  (rfl)

/-- The `N` subgroup of the pulled-back Tits system is the preimage of `N`. -/
@[simp]
theorem comap_subgroupN : (T.comap f hf).subgroupN = T.subgroupN.comap f :=
  (rfl)

/-- Membership in the `B` subgroup of the pulled-back Tits system. -/
theorem mem_comap_subgroupB {x : H} : x ∈ (T.comap f hf).subgroupB ↔ f x ∈ T.subgroupB := by
  rw [comap_subgroupB, Subgroup.mem_comap]

/-- Membership in the `N` subgroup of the pulled-back Tits system. -/
theorem mem_comap_subgroupN {x : H} : x ∈ (T.comap f hf).subgroupN ↔ f x ∈ T.subgroupN := by
  rw [comap_subgroupN, Subgroup.mem_comap]

/-- The Weyl group of the pulled-back Tits system is the Weyl group of the original one: the
class of `n ∈ f⁻¹(N)` corresponds to the class of `f n`. -/
noncomputable def comapWeylGroupMulEquiv : (T.comap f hf).WeylGroup ≃* T.WeylGroup :=
  MulEquiv.ofBijective (comapWeylGroupHom T (f := f))
    ⟨comapWeylGroupHom_injective T, comapWeylGroupHom_surjective T hf⟩

/-- The Weyl-group identification sends the class of `n` to the class of `f n`. -/
@[simp]
theorem comapWeylGroupMulEquiv_mk (n : (T.comap f hf).subgroupN) :
    T.comapWeylGroupMulEquiv f hf (QuotientGroup.mk n) =
      QuotientGroup.mk ⟨f n, (T.mem_comap_subgroupN f hf).mp n.2⟩ :=
  comapWeylGroupHom_mk T n

/-- The simple reflections of the pulled-back Tits system are the preimages of the simple
reflections of the original one under the identification of Weyl groups. -/
theorem comap_simple :
    (T.comap f hf).simple = T.comapWeylGroupMulEquiv f hf ⁻¹' T.simple :=
  (rfl)

end TauCeti.TitsSystem
