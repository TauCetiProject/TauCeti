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

An isomorphism carrying a subgroup `A` onto a subgroup `B` restricts to an isomorphism `↥A ≃* ↥B`,
and carries the coset space `G ⧸ A` bijectively onto `H ⧸ B`.
That restriction is `TauCeti.Subgroup.congrOfMapEq`, and every subgroup a construction transports
along an isomorphism — here the derived subgroup, elsewhere the fixed subgroup of an endomorphism —
uses it rather than repeating the composition of `MulEquiv.subgroupMap` with
`MulEquiv.subgroupCongr`.

## Main definitions

* `TauCeti.Subgroup.congrOfMapEq`: the isomorphism of subgroups restricted from an isomorphism of
  groups carrying the one onto the other.
* `MulEquiv.commutatorCongr`: its instance for the derived subgroup.
* `MonoidHom.subgroupCongr`: a homomorphism of subgroups transported along equalities of its
  domain and codomain, for reading a construction through two presentations of the subgroups it
  connects.
* `TauCeti.QuotientGroup.congrOfMapEq`: its coset-space companion — an isomorphism carrying `A`
  onto `B` gives a bijection `G ⧸ A ≃ H ⧸ B`. Neither subgroup need be normal, which is what
  distinguishes it from Mathlib's `QuotientGroup.congr`.

## Main results

* `TauCeti.MonoidHom.subgroupComap_injective_of_injective`: `f.subgroupComap K` is injective when
  `f` is.
* `QuotientGroup.congrOfSurjectiveOfKerLe`: coset spaces transport along a surjection whose
  kernel lies in the subgroup.
* `MonoidHom.center_le_ker`: the centre lies in the kernel of a surjection onto a
  centreless group.
* `TauCeti.Subgroup.map_commutator_eq_commutator`: a surjective homomorphism carries the derived
  subgroup onto the derived subgroup.
* `Subgroup.map_inf_comap`: the image of `H ⊓ f⁻¹(K)` is `f(H) ⊓ K`.
* `Subgroup.map_conj_map_conj`: successive conjugations of a subgroup compose to one
  conjugation.
* `Subgroup.map_map_conj`: the image of a conjugate subgroup is the conjugate of the image.
* `Subgroup.map_quotientGroupMap_map_mk'`: taking images in quotients commutes with the maps
  induced on quotients.
* `MonoidHom.subgroupCongr_injective`, `MonoidHom.subgroupCongr_surjective`: transport along
  equalities of the domain and codomain preserves injectivity and surjectivity.
* `Subgroup.subtype_comp_subgroupOfEquivOfLe`, `TauCeti.Subgroup.subtype_comp_congrOfMapEq`: the
  isomorphisms `subgroupOfEquivOfLe` and `congrOfMapEq` commute with the inclusions of subgroups.
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

/-- The centre of a group lies in the kernel of every surjection onto a centreless group.

Mathlib's `Subgroup.map_center_le_center` bounds the image of the centre under any surjection by
`Subgroup.center H`; this lemma is the special case where that bound is `⊥`. -/
theorem _root_.MonoidHom.center_le_ker (f : G →* H) (hf : Function.Surjective f)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G ≤ f.ker :=
  (Subgroup.map_eq_bot_iff _).mp <| le_bot_iff.mp <| hH ▸ Subgroup.map_center_le_center hf

/-- Along `A ≤ B`, the identification `Subgroup.subgroupOfEquivOfLe` of `A.subgroupOf B` with `A`
commutes with the inclusions into `G`. This is the homomorphism form of Mathlib's pointwise
`Subgroup.subgroupOfEquivOfLe_apply_coe`. -/
@[simp]
theorem _root_.Subgroup.subtype_comp_subgroupOfEquivOfLe {A B : Subgroup G} (h : A ≤ B) :
    A.subtype.comp (Subgroup.subgroupOfEquivOfLe h : A.subgroupOf B →* A) =
      B.subtype.comp (A.subgroupOf B).subtype :=
  MonoidHom.ext <| Subgroup.subgroupOfEquivOfLe_apply_coe h

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
        (by rw [MulEquiv.toMonoidHom_trans, ← _root_.Subgroup.map_map, h, h']) :=
  MulEquiv.ext fun _ => Subtype.ext (by simp)

/-- Restricting an isomorphism to subgroups commutes with the inclusions of the subgroups. This is
the homomorphism form of the pointwise `Subgroup.coe_congrOfMapEq_apply`. -/
@[simp]
theorem Subgroup.subtype_comp_congrOfMapEq (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) :
    B.subtype.comp (Subgroup.congrOfMapEq e h : A →* B) = (e : G →* H).comp A.subtype :=
  MonoidHom.ext <| Subgroup.coe_congrOfMapEq_apply e h

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

/-- The transported homomorphism takes the same value in the ambient group as the original does
at the corresponding element.

The equation is stated after coercion to `H` because its two sides land in the different subtypes
`↥B'` and `↥B`. As a `simp` lemma it moves the transport off the homomorphism and onto its
argument; `MonoidHom.subgroupCongr_id` and `MonoidHom.subgroupCongr_comp` rewrite the transported
homomorphism itself instead. -/
@[simp]
theorem _root_.MonoidHom.coe_subgroupCongr_apply {A A' : Subgroup G} {B B' : Subgroup H}
    (hA : A' = A) (hB : B' = B) (f : A →* B) (x : A') :
    (f.subgroupCongr hA hB x : H) = f ⟨x, hA ▸ x.2⟩ := by
  simp only [MonoidHom.subgroupCongr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_symm_apply]
  exact congrArg (fun y ↦ (f y : H)) (Subtype.ext (MulEquiv.subgroupCongr_apply hA x))

/-- Transporting the identity homomorphism along one equality of subgroups, on both sides, gives the
identity.

`MonoidHom.subgroupCongr` takes one equality at each end; they coincide here because the transported
map is an endomorphism. Both subgroups are pinned by the left-hand side, which is what makes this a
`simp` lemma where the composition companion `MonoidHom.subgroupCongr_comp` is not. -/
@[simp]
theorem _root_.MonoidHom.subgroupCongr_id {A A' : Subgroup G} (hA : A' = A) :
    (MonoidHom.id A).subgroupCongr hA hA = MonoidHom.id A' :=
  MonoidHom.ext (MulEquiv.subgroupCongr hA).symm_apply_apply

/-- Transport commutes with composition: transporting `g.comp f` along the outer two equalities
agrees with transporting `f` and `g` separately through a common middle subgroup.

Not a `simp` lemma: the middle subgroup `B'` and its presentation `hB` occur only on the
right-hand side, so `simp` would have to invent them and would rewrite into an unrelated
instantiation. `MonoidHom.subgroupCongr_id` is the identity companion. -/
theorem _root_.MonoidHom.subgroupCongr_comp {A A' : Subgroup G} {B B' : Subgroup H}
    {C C' : Subgroup K} (hA : A' = A) (hB : B' = B) (hC : C' = C) (f : A →* B) (g : B →* C) :
    (g.comp f).subgroupCongr hA hC = (g.subgroupCongr hB hC).comp (f.subgroupCongr hA hB) :=
  MonoidHom.ext fun _ ↦ Subtype.ext <| by simp

/-- Transport along equalities of the domain and codomain preserves injectivity.

The transport composes `f` with two isomorphisms, so it is injective exactly when `f` is; only the
direction a use site needs is recorded. `MonoidHom.subgroupCongr_surjective` is the companion for
surjectivity. -/
theorem _root_.MonoidHom.subgroupCongr_injective {A A' : Subgroup G} {B B' : Subgroup H}
    (hA : A' = A) (hB : B' = B) {f : A →* B} (hf : Function.Injective f) :
    Function.Injective (f.subgroupCongr hA hB) :=
  (MulEquiv.subgroupCongr hB).symm.injective.comp <| hf.comp (MulEquiv.subgroupCongr hA).injective

/-- Transport along equalities of the domain and codomain preserves surjectivity.

The transport composes `f` with two isomorphisms, so it is surjective exactly when `f` is; only the
direction a use site needs is recorded. `MonoidHom.subgroupCongr_injective` is the companion for
injectivity. -/
theorem _root_.MonoidHom.subgroupCongr_surjective {A A' : Subgroup G} {B B' : Subgroup H}
    (hA : A' = A) (hB : B' = B) {f : A →* B} (hf : Function.Surjective f) :
    Function.Surjective (f.subgroupCongr hA hB) :=
  (MulEquiv.subgroupCongr hB).symm.surjective.comp <| hf.comp (MulEquiv.subgroupCongr hA).surjective

/-! ## Transporting the derived subgroup -/

/-- A surjective homomorphism carries the derived subgroup onto the derived subgroup.

Without surjectivity only `≤` survives (Mathlib's `map_derivedSeries_le_derivedSeries`); Mathlib's
`Subgroup.map_commutator_eq` keeps an equality for an arbitrary `f`, at the cost of describing the
image as `⁅f.range, f.range⁆`. Reach for this lemma rather than `map_derivedSeries_eq` whenever the
derived subgroup is spelled `commutator`; `MulEquiv.commutatorCongr` below is the isomorphism it
unlocks. -/
theorem Subgroup.map_commutator_eq_commutator {f : G →* H} (hf : Function.Surjective f) :
    (commutator G).map f = commutator H :=
  -- `commutator G` is by definition `derivedSeries G 1`, so no rewriting is needed here.
  map_derivedSeries_eq hf 1

/-- The isomorphism of derived subgroups restricted from an isomorphism of groups.

This is `Subgroup.congrOfMapEq` for the derived subgroup: the map equality is supplied internally,
so a use site names only `e`, and the target is `commutator H` itself rather than the image
`(commutator G).map e` that `MulEquiv.subgroupMap` would land in. It acts as `e` on elements, and
its inverse as `e.symm`. -/
def _root_.MulEquiv.commutatorCongr (e : G ≃* H) : ↥(commutator G) ≃* ↥(commutator H) :=
  Subgroup.congrOfMapEq e <| Subgroup.map_commutator_eq_commutator e.surjective

/-- The restriction `MulEquiv.commutatorCongr e` to the derived subgroups agrees with `e` on
underlying
elements.

The equation is stated in the ambient group `H` because its two sides have the different types
`↥(commutator H)` and `H`. It is the derived-subgroup instance of `Subgroup.coe_congrOfMapEq_apply`,
which `simp` cannot apply on its own because it cannot see through `MulEquiv.commutatorCongr`;
`MulEquiv.coe_commutatorCongr_symm_apply` is the companion for the inverse, and Mathlib's
`MulEquiv.coe_subgroupMap_apply` says the same for the literal image `(commutator G).map e`. -/
@[simp]
theorem _root_.MulEquiv.coe_commutatorCongr_apply (e : G ≃* H) (x : ↥(commutator G)) :
    (MulEquiv.commutatorCongr e x : H) = e (x : G) :=
  Subgroup.coe_congrOfMapEq_apply e _ x

/-- The inverse of the restriction `MulEquiv.commutatorCongr e` to the derived subgroups agrees with
`e.symm` on underlying elements.

The equation is stated in the ambient group `G` because its two sides have the different types
`↥(commutator G)` and `G`. It is the derived-subgroup instance of
`Subgroup.coe_congrOfMapEq_symm_apply`, which `simp` cannot apply on its own because it cannot see
through `MulEquiv.commutatorCongr`; `MulEquiv.coe_commutatorCongr_apply` is the companion for the
forward direction,
`MulEquiv.commutatorCongr_symm` rewrites the whole inverse rather than a single value, and Mathlib's
`MulEquiv.subgroupMap_symm_apply` says the same for the literal image `(commutator G).map e` but
returns the subtype `⟨e.symm ↑y, _⟩` rather than its coercion. -/
@[simp]
theorem _root_.MulEquiv.coe_commutatorCongr_symm_apply (e : G ≃* H) (y : ↥(commutator H)) :
    ((MulEquiv.commutatorCongr e).symm y : G) = e.symm (y : H) :=
  Subgroup.coe_congrOfMapEq_symm_apply e _ y

/-- Restricting the identity isomorphism of `G` to the derived subgroup gives the identity of
`↥(commutator G)`.

The derived-subgroup instance of `Subgroup.congrOfMapEq_refl`, and a `simp` lemma in its own
right: `MulEquiv.commutatorCongr` does not unfold, so that general lemma never fires on this
left-hand side.
`MulEquiv.commutatorCongr_trans` and `MulEquiv.commutatorCongr_symm` are the companion composition
and inverse
statements; Mathlib's `abelianizationCongr_refl` is the same coherence for the abelianization. -/
@[simp]
theorem _root_.MulEquiv.commutatorCongr_refl :
    MulEquiv.commutatorCongr (MulEquiv.refl G) = MulEquiv.refl ↥(commutator G) :=
  Subgroup.congrOfMapEq_refl _

/-- Restricting to derived subgroups is functorial: the restriction of `e.trans f` is the composite
of the restrictions of `e` and of `f`.

The derived-subgroup instance of `Subgroup.congrOfMapEq_trans`, and a `simp` lemma in its own
right: `MulEquiv.commutatorCongr` does not unfold, so that general lemma never fires on this
left-hand side.
Both map equalities are supplied internally, so a use site names only `e` and `f`.
`MulEquiv.commutatorCongr_refl` and `MulEquiv.commutatorCongr_symm` are the companion identity
and inverse
statements; Mathlib's `abelianizationCongr_trans` is the same coherence for the abelianization. -/
@[simp]
theorem _root_.MulEquiv.commutatorCongr_trans (e : G ≃* H) (f : H ≃* K) :
    (MulEquiv.commutatorCongr e).trans (MulEquiv.commutatorCongr f) =
      MulEquiv.commutatorCongr (e.trans f) :=
  Subgroup.congrOfMapEq_trans e _ f _

-- Not `@[simp]`, for the reason given at `Subgroup.congrOfMapEq_symm`.
/-- Inverting the restriction of `e` to the derived subgroups gives the restriction of `e.symm`.

The derived-subgroup instance of `Subgroup.congrOfMapEq_symm`, whose map-equality hypothesis is
supplied internally, so a use site names only `e`. This is the whole-isomorphism form, for when the
inverse occurs as a map rather than applied to a point;
`MulEquiv.coe_commutatorCongr_symm_apply` is the
pointwise companion, and `MulEquiv.commutatorCongr_refl` and `MulEquiv.commutatorCongr_trans` are
the identity and
composition ones. Mathlib's `abelianizationCongr_symm` says the same for the abelianization. -/
theorem _root_.MulEquiv.commutatorCongr_symm (e : G ≃* H) :
    (MulEquiv.commutatorCongr e).symm = MulEquiv.commutatorCongr e.symm :=
  Subgroup.congrOfMapEq_symm e _

/-- The image of `H ⊓ f⁻¹(K)` under `f` is the part of `K` inside `f(H)`. -/
theorem _root_.Subgroup.map_inf_comap {G N : Type*} [Group G] [Group N]
    (H : Subgroup G) (K : Subgroup N) (f : G →* N) :
    (H ⊓ K.comap f).map f = H.map f ⊓ K := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap]
  exact ⟨fun ⟨x, ⟨hx, hxK⟩, hxy⟩ ↦ ⟨⟨x, hx, hxy⟩, hxy ▸ hxK⟩,
    fun ⟨⟨x, hx, hxy⟩, hy⟩ ↦ ⟨x, ⟨hx, hxy ▸ hy⟩, hxy⟩⟩

/-- The image of a conjugate subgroup `gRg⁻¹` under a homomorphism `f` is the conjugate of `f(R)`
by `f g`.

Stated with `Subgroup.map (MulAut.conj _).toMonoidHom`, not the pointwise `MulAut.conj _ • _`:
the two are definitionally equal (`Subgroup.pointwise_smul_def` is `rfl`) and Mathlib supplies no
rewrite between them, so a use site in either spelling can apply this. It is `Subgroup.map_map`
specialized to an inner conjugation, while `Subgroup.Normal.map_conj_eq` is the degenerate case
in which conjugation fixes the subgroup instead of moving it. -/
theorem _root_.Subgroup.map_map_conj (R : Subgroup G) (f : G →* H) (g : G) :
    (R.map (MulAut.conj g).toMonoidHom).map f = (R.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  -- conjugation is natural: `f ∘ conj g` and `conj (f g) ∘ f` agree pointwise
  exact congrArg (Subgroup.map · R) (MonoidHom.ext fun x ↦ by simp)

/-- Conjugating a subgroup first by `g` and then by `h` is conjugation by `h * g`. -/
theorem _root_.Subgroup.map_conj_map_conj (R : Subgroup G) (g h : G) :
    (R.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      R.map (MulAut.conj (h * g)).toMonoidHom := by
  simp only [Subgroup.map_map, MulEquiv.toMonoidHom_eq_coe,
    ← MulEquiv.toMonoidHom_trans, ← MulAut.mul_def, ← map_mul]

/-- The image of a subgroup in `G ⧸ N`, pushed forward along the map `G ⧸ N →* H ⧸ M` induced by
`f`, is the image in `H ⧸ M` of the image of the subgroup under `f`.

The subgroup-image form of Mathlib's pointwise `QuotientGroup.map_mk'`. `R` need not be related to
`N` or `M`. As a `simp` lemma it fires left to right, so the normal form of an image taken in a
quotient is "push down along `f` first, project afterwards", and `QuotientGroup.map` disappears.
`Subgroup.map_map_conj` above is the same commuting square for conjugation. -/
@[simp]
theorem _root_.Subgroup.map_quotientGroupMap_map_mk' (R : Subgroup G) {N : Subgroup G}
    {M : Subgroup H} [N.Normal] [M.Normal] (f : G →* H) (h : N ≤ M.comap f) :
    (R.map (QuotientGroup.mk' N)).map (QuotientGroup.map N M f h) =
      (R.map f).map (QuotientGroup.mk' M) := by
  have hf : (QuotientGroup.map N M f h).comp (QuotientGroup.mk' N) =
      (QuotientGroup.mk' M).comp f :=
    MonoidHom.ext fun x ↦ QuotientGroup.map_mk' N M f h x
  rw [Subgroup.map_map, Subgroup.map_map, hf]

/-! ## Transporting a coset space along an isomorphism -/

/-- **Coset spaces transport along an isomorphism.** If `e : G ≃* H` carries `A` onto `B`, then
`G ⧸ A ≃ H ⧸ B`, by `e` on representatives.

Neither subgroup is assumed normal, so this is an equivalence of coset *spaces*.
`QuotientGroup.congr` is the normal case, where the same data upgrades to a `MulEquiv`; it does
not apply to a subgroup like `Γ₁ ∩ gΓ₂g⁻¹`, which is where this is needed. It is the coset-space
companion of `Subgroup.congrOfMapEq` above.

Both subgroups are implicit and pinned by `h`, so neither is named at a use site, unlike
`QuotientGroup.congr`. `QuotientGroup.congrOfMapEq_mk` is the `@[simp]` lemma that computes it on
representatives, and `QuotientGroup.congrOfSurjectiveOfKerLe` below is the version for a map that
is only surjective. -/
def QuotientGroup.congrOfMapEq (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) : G ⧸ A ≃ H ⧸ B :=
  Quotient.congr e.toEquiv fun a b ↦ by
    simp [← h, QuotientGroup.leftRel_apply, ← map_inv, ← map_mul]

/-- **`QuotientGroup.congrOfMapEq` acts by `e` on representatives**: the transported coset of `a`
is the coset of `e a`.

Downstream this lemma is not optional: `congrOfMapEq` is not `@[expose]`d, so outside this module
the two sides are not definitionally equal and neither `rfl` nor the underlying `Quotient.congr_mk`
closes the goal. `QuotientGroup.congr_mk` is Mathlib's version for *normal* subgroups, where the
equivalence upgrades to a `MulEquiv`. -/
@[simp]
theorem QuotientGroup.congrOfMapEq_mk (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) (a : G) :
    QuotientGroup.congrOfMapEq e h (QuotientGroup.mk a) = QuotientGroup.mk (e a) := by rfl

/-- **Coset spaces transport along a surjection whose kernel lies in the subgroup.** For `ψ`
surjective with `ker ψ ≤ A` and `A.map ψ = B`, the map `G ⧸ A → H ⧸ B` induced by `ψ` on
representatives is a bijection.

Injectivity of `ψ` is not needed: `ker ψ ≤ A` makes the denominator absorb the kernel, so the
index is unchanged. That is what lets a Hecke decomposition be carried into a group acting
faithfully on the upper half-plane, where the collapsing of `±1` is the point rather than a
defect. As with `QuotientGroup.congrOfMapEq`, neither subgroup need be normal. -/
noncomputable def QuotientGroup.congrOfSurjectiveOfKerLe (ψ : G →* H)
    (hsurj : Function.Surjective ψ) {A : Subgroup G} {B : Subgroup H}
    (hker : ψ.ker ≤ A) (hmap : A.map ψ = B) : G ⧸ A ≃ H ⧸ B := by
  classical
  -- `ker ψ ≤ A` is exactly what makes `A` the full preimage of `B`, and membership in a preimage
  -- is the whole content of the coset relation matching on both sides
  have hcomap : B.comap ψ = A := hmap ▸ Subgroup.comap_map_eq_self hker
  have key : ∀ a b : G, (a⁻¹ * b ∈ A) ↔ ((ψ a)⁻¹ * ψ b ∈ B) := fun a b ↦ by
    rw [← hcomap, Subgroup.mem_comap, map_mul, map_inv]
  refine Equiv.ofBijective (Quotient.map' ψ ?_) ⟨?_, ?_⟩
  · intro a b hab
    exact QuotientGroup.leftRel_apply.mpr
      ((key a b).mp (QuotientGroup.leftRel_apply.mp hab))
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | _ a =>
    induction y using QuotientGroup.induction_on with | _ b =>
    exact QuotientGroup.eq.mpr ((key a b).mpr (QuotientGroup.eq.mp hxy))
  · exact Quotient.map_surjective _ hsurj

@[simp]
theorem QuotientGroup.congrOfSurjectiveOfKerLe_mk (ψ : G →* H)
    (hsurj : Function.Surjective ψ) {A : Subgroup G} {B : Subgroup H}
    (hker : ψ.ker ≤ A) (hmap : A.map ψ = B) (a : G) :
    QuotientGroup.congrOfSurjectiveOfKerLe ψ hsurj hker hmap (QuotientGroup.mk a) =
      QuotientGroup.mk (ψ a) := by
  -- This lemma IS the abstraction barrier: `congrOfSurjectiveOfKerLe` is an `Equiv.ofBijective`
  -- around `Quotient.map' ψ`, whose `toFun` is that map, so on a class `⟦a⟧` it reduces to
  -- `⟦ψ a⟧` — the content of Mathlib's `Quotient.map'_mk''`, which cannot be cited directly here
  -- because `Equiv.ofBijective` has no `_apply` lemma in Mathlib to strip the wrapper first
  -- (checked: only `Equiv.ofBijective_apply_symm_apply` exists). Downstream code rewrites with
  -- this lemma and never sees either wrapper, which is what keeps the implementation free to move.
  unfold QuotientGroup.congrOfSurjectiveOfKerLe
  rfl

end TauCeti
