/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Maps of subgroups

Mathlib's `MonoidHom.subgroupComap` sends the preimage `K.comap f` of a subgroup `K` to `K`.
Mathlib records that this map is surjective when `f` is
(`MonoidHom.subgroupComap_surjective_of_surjective`); this file records the companion fact for
injectivity. It also records how surjective homomorphisms act on centres and on derived subgroups.

An isomorphism carrying a subgroup `A` onto a subgroup `B` restricts to an isomorphism `↥A ≃* ↥B`.
That restriction is `TauCeti.Subgroup.congrOfMapEq`, and every subgroup a construction transports
along an isomorphism — here the derived subgroup, elsewhere the fixed subgroup of an endomorphism —
uses it rather than repeating the composition of `MulEquiv.subgroupMap` with
`MulEquiv.subgroupCongr`.

## Main definitions

* `TauCeti.Subgroup.congrOfMapEq`: the isomorphism of subgroups restricted from an isomorphism of
  groups carrying the one onto the other.
* `TauCeti.commutatorCongr`: its instance for the derived subgroup.
* `MonoidHom.subgroupCongr`: a homomorphism of subgroups transported along equalities of its
  domain and codomain, for reading a construction through two presentations of the subgroups it
  connects.

## Main results

* `TauCeti.MonoidHom.subgroupComap_injective_of_injective`: `f.subgroupComap K` is injective when
  `f` is.
* `TauCeti.Subgroup.map_center_le`: a surjective homomorphism carries central elements to central
  elements.
* `MonoidHom.center_le_ker`: the centre lies in the kernel of a surjection onto a
  centreless group.
* `TauCeti.Subgroup.map_commutator_eq_commutator`: a surjective homomorphism carries the derived
  subgroup onto the derived subgroup.
* `Subgroup.map_conj_map`: the image of a conjugate subgroup is the conjugate of the image.
* `Subgroup.map_mk'_map_quotientGroupMap`: taking images in quotients commutes with the maps
  induced on quotients.
-/

public section

namespace TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- The comparison map from the preimage of a subgroup to that subgroup is injective as soon as the
underlying homomorphism is. Companion to Mathlib's
`MonoidHom.subgroupComap_surjective_of_surjective`. -/
theorem MonoidHom.subgroupComap_injective_of_injective {f : H →* G} (hf : Function.Injective f)
    (K : Subgroup G) : Function.Injective (f.subgroupComap K) :=
  fun _ _ hxy => Subtype.ext (hf (congrArg Subtype.val hxy))

/-- A surjective homomorphism carries central elements to central elements. -/
theorem Subgroup.map_center_le (f : G →* H) (hf : Function.Surjective f) :
    (Subgroup.center G).map f ≤ Subgroup.center H := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨z, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]

/-- An isomorphism of groups carries the centre onto the centre. -/
theorem Subgroup.map_center_eq_center (e : G ≃* H) :
    (Subgroup.center G).map (e : G →* H) = Subgroup.center H := by
  apply le_antisymm (Subgroup.map_center_le _ e.surjective)
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  exact Subgroup.map_center_le (e.symm : H →* G) e.symm.surjective ⟨y, hy, rfl⟩

/-- The centre of a group lies in the kernel of every surjection onto a centreless group. -/
theorem _root_.MonoidHom.center_le_ker (f : G →* H) (hf : Function.Surjective f)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G ≤ f.ker := by
  intro x hx
  have hfx := Subgroup.map_center_le f hf ⟨x, hx, rfl⟩
  rw [hH, Subgroup.mem_bot] at hfx
  exact hfx

/-! ## Restricting an isomorphism to a subgroup -/

variable {K : Type*} [Group K]

/-- The isomorphism of subgroups restricted from an isomorphism of groups carrying the one onto the
other. -/
def Subgroup.congrOfMapEq (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) : ↥A ≃* ↥B :=
  (e.subgroupMap A).trans (MulEquiv.subgroupCongr h)

@[simp]
theorem Subgroup.coe_congrOfMapEq_apply (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) (x : ↥A) : (Subgroup.congrOfMapEq e h x : H) = e (x : G) := by
  simp only [Subgroup.congrOfMapEq, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply]

@[simp]
theorem Subgroup.coe_congrOfMapEq_symm_apply (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) (y : ↥B) :
    ((Subgroup.congrOfMapEq e h).symm y : G) = e.symm (y : H) := by
  simp only [Subgroup.congrOfMapEq, MulEquiv.symm_trans_apply, MulEquiv.subgroupCongr_symm_apply,
    MulEquiv.subgroupMap_symm_apply]

@[simp]
theorem Subgroup.congrOfMapEq_refl {A : Subgroup G}
    (h : A.map (MulEquiv.refl G : G →* G) = A) :
    Subgroup.congrOfMapEq (MulEquiv.refl G) h = MulEquiv.refl ↥A :=
  MulEquiv.ext fun _ => Subtype.ext (by simp)

@[simp]
theorem Subgroup.congrOfMapEq_trans (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) (f : H ≃* K) {C : Subgroup K}
    (h' : B.map (f : H →* K) = C) :
    (Subgroup.congrOfMapEq e h).trans (Subgroup.congrOfMapEq f h') =
      Subgroup.congrOfMapEq (e.trans f)
        (by rw [MulEquiv.coe_monoidHom_trans, ← _root_.Subgroup.map_map, h, h']) :=
  MulEquiv.ext fun _ => Subtype.ext (by simp)

-- Not `@[simp]`: with this in the simp set, `Subgroup.coe_congrOfMapEq_symm_apply` below is
-- provable by `simp`, which the `simpNF` linter rejects.
theorem Subgroup.congrOfMapEq_symm (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) :
    (Subgroup.congrOfMapEq e h).symm =
      Subgroup.congrOfMapEq e.symm ((_root_.Subgroup.map_symm_eq_iff_map_eq A).mpr h) :=
  MulEquiv.ext fun _ => Subtype.ext (by simp)

/-- The homomorphism of subgroups obtained from a homomorphism between two other subgroups by
transporting along equalities of the domain and of the codomain. -/
def _root_.MonoidHom.subgroupCongr {A A' : Subgroup G} {B B' : Subgroup H}
    (hA : A' = A) (hB : B' = B) (f : A →* B) : A' →* B' :=
  ((MulEquiv.subgroupCongr hB).symm.toMonoidHom).comp
    (f.comp (MulEquiv.subgroupCongr hA).toMonoidHom)

@[simp]
theorem _root_.MonoidHom.coe_subgroupCongr_apply {A A' : Subgroup G} {B B' : Subgroup H}
    (hA : A' = A) (hB : B' = B) (f : A →* B) (x : A') :
    (f.subgroupCongr hA hB x : H) = f ⟨x, hA ▸ x.2⟩ :=
  (rfl)

@[simp]
theorem _root_.MonoidHom.subgroupCongr_id {A A' : Subgroup G} (hA : A' = A) :
    (MonoidHom.id A).subgroupCongr hA hA = MonoidHom.id A' :=
  MonoidHom.ext fun x => (MulEquiv.subgroupCongr hA).symm_apply_apply x

-- Not `@[simp]`: the middle subgroup `B'` and its presentation `hB` occur only on the
-- right-hand side, so `simp` would have to invent them and would rewrite into an unrelated
-- instantiation.
theorem _root_.MonoidHom.subgroupCongr_comp {A A' : Subgroup G} {B B' : Subgroup H}
    {C C' : Subgroup K} (hA : A' = A) (hB : B' = B) (hC : C' = C) (f : A →* B) (g : B →* C) :
    (g.comp f).subgroupCongr hA hC = (g.subgroupCongr hB hC).comp (f.subgroupCongr hA hB) :=
  MonoidHom.ext fun x => by
    simp only [MonoidHom.subgroupCongr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]

theorem _root_.MonoidHom.subgroupCongr_injective {A A' : Subgroup G} {B B' : Subgroup H}
    (hA : A' = A) (hB : B' = B) {f : A →* B} (hf : Function.Injective f) :
    Function.Injective (f.subgroupCongr hA hB) :=
  (MulEquiv.subgroupCongr hB).symm.injective.comp
    (hf.comp (MulEquiv.subgroupCongr hA).injective)

/-! ## Transporting the derived subgroup -/

/-- A surjective homomorphism carries the derived subgroup onto the derived subgroup. -/
theorem Subgroup.map_commutator_eq_commutator {f : G →* H} (hf : Function.Surjective f) :
    (commutator G).map f = commutator H := by
  simpa using map_derivedSeries_eq hf 1

/-- The isomorphism of derived subgroups restricted from an isomorphism of groups. -/
def commutatorCongr (e : G ≃* H) : ↥(commutator G) ≃* ↥(commutator H) :=
  Subgroup.congrOfMapEq e (Subgroup.map_commutator_eq_commutator e.surjective)

@[simp]
theorem coe_commutatorCongr_apply (e : G ≃* H) (x : ↥(commutator G)) :
    (commutatorCongr e x : H) = e (x : G) :=
  Subgroup.coe_congrOfMapEq_apply e _ x

@[simp]
theorem coe_commutatorCongr_symm_apply (e : G ≃* H) (y : ↥(commutator H)) :
    ((commutatorCongr e).symm y : G) = e.symm (y : H) :=
  Subgroup.coe_congrOfMapEq_symm_apply e _ y

@[simp]
theorem commutatorCongr_refl :
    commutatorCongr (MulEquiv.refl G) = MulEquiv.refl ↥(commutator G) :=
  Subgroup.congrOfMapEq_refl _

@[simp]
theorem commutatorCongr_trans (e : G ≃* H) (f : H ≃* K) :
    (commutatorCongr e).trans (commutatorCongr f) = commutatorCongr (e.trans f) :=
  Subgroup.congrOfMapEq_trans e _ f _

-- Not `@[simp]`, for the reason given at `Subgroup.congrOfMapEq_symm`.
theorem commutatorCongr_symm (e : G ≃* H) :
    (commutatorCongr e).symm = commutatorCongr e.symm :=
  Subgroup.congrOfMapEq_symm e _

/-- The image of a conjugate subgroup `gRg⁻¹` under a homomorphism `f` is the conjugate of `f(R)`
by `f g`. -/
theorem _root_.Subgroup.map_conj_map (R : Subgroup G) (f : G →* H) (g : G) :
    (R.map (MulAut.conj g).toMonoidHom).map f = (R.map f).map (MulAut.conj (f g)).toMonoidHom := by
  have hf : f.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (f g)).toMonoidHom.comp f :=
    MonoidHom.ext fun x ↦ by simp
  rw [Subgroup.map_map, Subgroup.map_map, hf]

/-- The image of a subgroup in `G ⧸ N`, pushed forward along the map `G ⧸ N →* H ⧸ M` induced by
`f`, is the image in `H ⧸ M` of the image of the subgroup under `f`. -/
@[simp]
theorem _root_.Subgroup.map_mk'_map_quotientGroupMap (R : Subgroup G) {N : Subgroup G}
    {M : Subgroup H} [N.Normal] [M.Normal] (f : G →* H) (h : N ≤ M.comap f) :
    (R.map (QuotientGroup.mk' N)).map (QuotientGroup.map N M f h) =
      (R.map f).map (QuotientGroup.mk' M) := by
  have hf : (QuotientGroup.map N M f h).comp (QuotientGroup.mk' N) =
      (QuotientGroup.mk' M).comp f :=
    MonoidHom.ext fun x ↦ QuotientGroup.map_mk' N M f h x
  rw [Subgroup.map_map, Subgroup.map_map, hf]

end TauCeti
