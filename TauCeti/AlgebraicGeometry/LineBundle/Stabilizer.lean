/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.GroupTheory.GroupAction.Stabilizer.MulDistribMulAction

/-!
# Automorphisms acting on line-bundle classes, and their stabilizers

The automorphism group `Aut X` of a scheme `X` acts on the group `LineBundleClass X` of
isomorphism classes of line bundles by inverse pullback, `g • [L] = [(g⁻¹)^* L]`. Automorphisms
compose as maps, `g * h = g ∘ h`, and pullback reverses composition, `(g ∘ h)^* = h^* ∘ g^*`, so it
is inverse pullback, not pullback, that is a left action. The action is by group automorphisms,
since pullback is a homomorphism of Picard groups. An automorphism fixes a class under inverse
pullback exactly when it fixes it under pullback, so both conventions have the same stabilizers.

For a morphism `f : X ⟶ S`, the automorphisms of `X` over `S` are the group `Aut (Over.mk f)`.
The subgroup `f.autStabilizer a` of those whose pullback fixes the class `a` is the stabilizer of
`a` for this action; its members are characterized by `g^* a = a`, and for the class of an actual
line bundle `L` by the existence of an isomorphism `g^* L ≅ L`, with no isomorphism chosen. When
`a` is ample, this is the group `Aut(X, [L])` of automorphisms of a polarized scheme over `S`. The
stabilizer of the trivial class is the whole group, the stabilizer of `a⁻¹` is that
of `a`, and in a torsion-free Picard group the stabilizer of `a ^ n` is that of `a` for every
`n ≠ 0`. An isomorphism of schemes over `S` matching two classes identifies their stabilizers by
conjugation.

## Main declarations

* the instance `MulDistribMulAction (Aut X) (LineBundleClass X)`, with
  `TauCeti.AlgebraicGeometry.LineBundleClass.smul_def`: `g • a = (g⁻¹)^* a`;
* `AlgebraicGeometry.Scheme.Hom.autStabilizer f a`: the automorphisms of `X` over `S` whose
  pullback fixes `a`, with `Scheme.Hom.mem_autStabilizer_iff` and
  `Scheme.Hom.mem_autStabilizer_mk_iff`;
* `Scheme.Hom.autStabilizer_pow`: the stabilizer of `a ^ n` is that of `a` when the Picard group
  is torsion-free and `n ≠ 0`;
* `Scheme.Hom.autStabilizerEquivOfIso`: an isomorphism over `S` matching two classes induces an
  isomorphism of their stabilizers.

## References

* S. Rizov, *Moduli stacks of polarized K3 surfaces in mixed characteristic*, §3.3, the
  definition following Remark 3.3.2.
* D. Huybrechts, *Lectures on K3 Surfaces*, Chapter 5, §3.
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace LineBundleClass

variable {X : Scheme.{u}}

/-- The automorphism group of a scheme acts on its line-bundle classes by inverse pullback,
`g • [L] = [(g⁻¹)^* L]`. This is a left action because automorphisms compose as maps while
pullback reverses composition. It acts by group automorphisms of the Picard group. -/
instance : MulDistribMulAction (Aut X) (LineBundleClass X) where
  smul g a := pullback g.asIso.inv a
  one_smul := pullback_id
  mul_smul g h a := (pullback_comp g.asIso.inv h.asIso.inv a).symm
  smul_mul g := pullback_mul g.asIso.inv
  smul_one g := pullback_one g.asIso.inv

/-- An automorphism acts on line-bundle classes by pullback along its inverse. -/
@[simp]
lemma smul_def (g : Aut X) (a : LineBundleClass X) : g • a = pullback g.asIso.inv a :=
  (rfl)

/-- An automorphism fixes a line-bundle class under inverse pullback exactly when it fixes it
under pullback. -/
lemma smul_eq_self_iff (g : Aut X) (a : LineBundleClass X) :
    g • a = a ↔ pullback g.asIso.hom a = a := by
  rw [smul_eq_iff_eq_inv_smul, eq_comm, smul_def, Aut.inv_asIso, Iso.symm_inv]

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

universe u

variable {X X' S : Scheme.{u}} (f : X ⟶ S) {f' : X' ⟶ S}

/-- The **stabilizer** of a line-bundle class `a` on `X` in the automorphism group of `X` over
`S`, for a morphism `f : X ⟶ S`: the automorphisms `g` of `X` over `S` with `g^* a = a`. It is the
stabilizer of `a` under the action of `Aut X` on line-bundle classes by inverse pullback, pulled
back to `Aut (Over.mk f)`. For the class of a line bundle `L`, membership records the existence of
an isomorphism `g^* L ≅ L`, but no chosen isomorphism (`mem_autStabilizer_mk_iff`). When `a` is
ample, this is the automorphism group `Aut(X, [L])` of the polarized scheme over `S`. -/
noncomputable def autStabilizer (a : LineBundleClass X) : Subgroup (Aut (Over.mk f)) :=
  (MulAction.stabilizer (Aut X) a).comap ((Over.forget S).mapAut (Over.mk f))

/-- The stabilizer of `a` in `Aut (Over.mk f)` is the preimage of the stabilizer of `a` in `Aut X`
under the forgetful homomorphism. -/
lemma autStabilizer_eq_comap (a : LineBundleClass X) :
    f.autStabilizer a =
      (MulAction.stabilizer (Aut X) a).comap ((Over.forget S).mapAut (Over.mk f)) :=
  (rfl)

/-- An automorphism of `X` over `S` stabilizes a line-bundle class `a` exactly when its pullback
fixes `a`. -/
@[simp]
lemma mem_autStabilizer_iff {a : LineBundleClass X} {g : Aut (Over.mk f)} :
    g ∈ f.autStabilizer a ↔ LineBundleClass.pullback g.asIso.hom.left a = a := by
  rw [autStabilizer_eq_comap, Subgroup.mem_comap]
  refine (MulAction.mem_stabilizer_iff (G := Aut X)).trans ?_
  rw [LineBundleClass.smul_eq_self_iff, Functor.mapAut_apply_asIso, Functor.mapIso_hom,
    Over.forget_map]

/-- An automorphism of `X` over `S` stabilizes a line-bundle class `a` exactly when pullback
along its inverse fixes `a`. -/
lemma mem_autStabilizer_iff_pullback_inv {a : LineBundleClass X} {g : Aut (Over.mk f)} :
    g ∈ f.autStabilizer a ↔ LineBundleClass.pullback g.asIso.inv.left a = a := by
  rw [autStabilizer_eq_comap, Subgroup.mem_comap]
  refine (MulAction.mem_stabilizer_iff (G := Aut X)).trans ?_
  rw [LineBundleClass.smul_def, Functor.mapAut_apply_asIso, Functor.mapIso_inv, Over.forget_map]

/-- An automorphism `g` of `X` over `S` stabilizes the class of a line bundle `L` exactly when
`g^* L` is isomorphic to `L`. -/
lemma mem_autStabilizer_mk_iff {L : InvertibleSheaf X} {g : Aut (Over.mk f)} :
    g ∈ f.autStabilizer (LineBundleClass.mk L) ↔
      Nonempty (((InvertibleSheaf.pullback g.asIso.hom.left).obj L).obj ≅ L.obj) := by
  rw [mem_autStabilizer_iff, LineBundleClass.pullback_mk, LineBundleClass.mk_eq_mk_iff]

/-- Every automorphism over `S` stabilizes the trivial line-bundle class. -/
@[simp]
lemma autStabilizer_one : f.autStabilizer 1 = ⊤ := by
  rw [autStabilizer_eq_comap, MulAction.stabilizer_one, Subgroup.comap_top]

/-- A line-bundle class and its inverse have the same stabilizer. -/
@[simp]
lemma autStabilizer_inv (a : LineBundleClass X) : f.autStabilizer a⁻¹ = f.autStabilizer a := by
  rw [autStabilizer_eq_comap, autStabilizer_eq_comap, MulAction.stabilizer_inv]

/-- An automorphism stabilizing two line-bundle classes stabilizes their product. -/
lemma autStabilizer_inf_autStabilizer_le_autStabilizer_mul (a b : LineBundleClass X) :
    f.autStabilizer a ⊓ f.autStabilizer b ≤ f.autStabilizer (a * b) := by
  simp only [autStabilizer_eq_comap, ← Subgroup.comap_inf]
  exact Subgroup.comap_mono (MulAction.stabilizer_inf_stabilizer_le_stabilizer_mul a b)

/-- An automorphism stabilizing a line-bundle class stabilizes all of its integer powers. -/
lemma le_autStabilizer_zpow (a : LineBundleClass X) (n : ℤ) :
    f.autStabilizer a ≤ f.autStabilizer (a ^ n) :=
  Subgroup.comap_mono (MulAction.le_stabilizer_zpow a n)

/-- An automorphism stabilizing a line-bundle class stabilizes all of its natural powers. -/
lemma le_autStabilizer_pow (a : LineBundleClass X) (n : ℕ) :
    f.autStabilizer a ≤ f.autStabilizer (a ^ n) :=
  Subgroup.comap_mono (MulAction.le_stabilizer_pow a n)

/-- In a torsion-free Picard group, a line-bundle class and its nonzero integer powers have the
same stabilizer: if `(g^* a) ^ n = a ^ n` then `g^* a = a`. -/
lemma autStabilizer_zpow [IsMulTorsionFree (LineBundleClass X)] (a : LineBundleClass X) {n : ℤ}
    (hn : n ≠ 0) : f.autStabilizer (a ^ n) = f.autStabilizer a := by
  have := IsMulTorsionFree.hasUniqueRoots (M := LineBundleClass X)
  rw [autStabilizer_eq_comap, autStabilizer_eq_comap, MulAction.stabilizer_zpow a hn]

/-- In a torsion-free Picard group, a line-bundle class and its nonzero natural powers have the
same stabilizer. In particular, an ample class and its positive multiples define the same
polarized automorphism group. -/
lemma autStabilizer_pow [IsMulTorsionFree (LineBundleClass X)] (a : LineBundleClass X) {n : ℕ}
    (hn : n ≠ 0) : f.autStabilizer (a ^ n) = f.autStabilizer a := by
  have := IsMulTorsionFree.hasUniqueRoots (M := LineBundleClass X)
  rw [autStabilizer_eq_comap, autStabilizer_eq_comap, MulAction.stabilizer_pow a hn]

/-- Conjugation by an isomorphism `e` of schemes over `S` carries the stabilizer of a class `a`
onto the stabilizer of every class `a'` with `e^* a' = a`. -/
lemma map_autStabilizer_autMulEquivOfIso (e : Over.mk f ≅ Over.mk f') {a : LineBundleClass X}
    {a' : LineBundleClass X'} (ha : LineBundleClass.pullback e.hom.left a' = a) :
    (f.autStabilizer a).map (Aut.autMulEquivOfIso e).toMonoidHom = f'.autStabilizer a' := by
  -- Pullback along `e.hom.left` is a group isomorphism with inverse pullback along `e.inv.left`.
  let E := LineBundleClass.pullbackEquiv ((Over.forget S).mapIso e)
  have hE (b : LineBundleClass X') : E b = LineBundleClass.pullback e.hom.left b := by
    rw [LineBundleClass.pullbackEquiv_apply, Functor.mapIso_hom, Over.forget_map]
  have hEs (b : LineBundleClass X) : E.symm b = LineBundleClass.pullback e.inv.left b := by
    rw [LineBundleClass.pullbackEquiv_symm, LineBundleClass.pullbackEquiv_apply, Iso.symm_hom,
      Functor.mapIso_inv, Over.forget_map]
  have ha' : a' = E.symm a := E.eq_symm_apply.2 ((hE a').trans ha)
  ext g'
  obtain ⟨g, rfl⟩ := (Aut.autMulEquivOfIso e).surjective g'
  -- The inverse of the conjugate `e ∘ g ∘ e⁻¹` is `e ∘ g⁻¹ ∘ e⁻¹`.
  have hconj : (Aut.autMulEquivOfIso e g).asIso.inv.left =
      e.inv.left ≫ g.asIso.inv.left ≫ e.hom.left := by
    simp only [Aut.autMulEquivOfIso_apply_asIso, Iso.trans_inv, Iso.symm_inv, Over.comp_left,
      Category.assoc]
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_autStabilizer_iff_pullback_inv,
    mem_autStabilizer_iff_pullback_inv, hconj]
  -- Pulling back along `e.inv ≫ g⁻¹ ≫ e.hom` is `E.symm ∘ g⁻¹^* ∘ E`, and `E a' = a`.
  rw [← LineBundleClass.pullback_comp, ← LineBundleClass.pullback_comp, ha, ← hEs, ha',
    E.symm.apply_eq_iff_eq]

/-- An isomorphism `e` of schemes over `S` with `e^* a' = a` induces, by conjugation, an
isomorphism between the stabilizer of `a` and the stabilizer of `a'`: an isomorphism of polarized
schemes gives an isomorphism of their polarized automorphism groups. -/
noncomputable def autStabilizerEquivOfIso (e : Over.mk f ≅ Over.mk f') {a : LineBundleClass X}
    {a' : LineBundleClass X'} (ha : LineBundleClass.pullback e.hom.left a' = a) :
    f.autStabilizer a ≃* f'.autStabilizer a' :=
  ((Aut.autMulEquivOfIso e).subgroupMap _).trans
    (MulEquiv.subgroupCongr (f.map_autStabilizer_autMulEquivOfIso e ha))

/-- The isomorphism `autStabilizerEquivOfIso e ha` is conjugation by `e`. -/
@[simp]
lemma coe_autStabilizerEquivOfIso_apply (e : Over.mk f ≅ Over.mk f') {a : LineBundleClass X}
    {a' : LineBundleClass X'} (ha : LineBundleClass.pullback e.hom.left a' = a)
    (g : f.autStabilizer a) :
    (f.autStabilizerEquivOfIso e ha g : Aut (Over.mk f')) = Aut.autMulEquivOfIso e g :=
  (rfl)

end AlgebraicGeometry.Scheme.Hom
