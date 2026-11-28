/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Galois.Torsor.Stalk

/-!
# Torsors on finite continuous `G`-sets are classified by continuous nonabelian `H¹`

Let `G` be a compact topological group (for instance a profinite Galois group) and `𝒢` a sheaf of
groups on the finite continuous `G`-sets `ContAction FintypeCat G` with the jointly surjective
topology, and write `A` for its stalk at the point `ContAction.point G`, a group with a smooth
action of `G` by group automorphisms. Taking stalks sends the classes of `𝒢`-torsors to the
continuous nonabelian `H¹(G, A)` (`ContAction.nonabelianH1ToStalk`). This file shows that, for
the discrete topology on `A`, this map is a bijection (`ContAction.nonabelianH1ToStalk_bijective`,
`ContAction.nonabelianH1EquivStalk`): torsors under the sheaf of groups of a smooth `G`-group are
classified by Galois cocycles.

The inverse is built from the equivalence `ContAction.sheafEquiv` between sheaves of sets and
smooth `G`-sets. A smooth `(G, A)`-torsor `T` gives the sheaf of `G`-maps into `T`
(`ContAction.torsorOfSmoothTorsor T`). A section `a` of `𝒢` over `S` acts on a `G`-map
`φ : S → T` pointwise through its germs, `(a • φ)(s) = [a]_s • φ(s)`, which is again a `G`-map
because `g • (b • x) = (g • b) • (g • x)`. Simple transitivity follows from that of `A` on `T`,
since sections of `𝒢` are the `G`-maps into `A` (`ContAction.exists_grpGerm_eq` and
`ContAction.grpGerm_ext`), and the sheaf is locally nonempty because every point of `T` lies in
a finite orbit. Evaluation of germs identifies the stalk of this torsor with `T`, compatibly with
both actions, so it has the class of `T`
(`ContAction.cls_torsorStalkSmoothTorsor_torsorOfSmoothTorsor`).

Conversely, an isomorphism of the stalks of two `𝒢`-torsors as smooth torsors is a morphism of
smooth `G`-sets, so it comes from a morphism of the underlying sheaves (taking stalks is fully
faithful, `ContAction.fromSheafFullyFaithful`). That morphism commutes with the action of `𝒢`
because it does so on germs, so it is a morphism of torsors (`ContAction.torsorHomOfIso`).

## Main definitions

* `ContAction.torsorOfSmoothTorsor T`: the `𝒢`-torsor of `G`-maps into a smooth torsor `T`
  under the stalk of `𝒢`.
* `ContAction.torsorHomOfIso e`: the morphism of `𝒢`-torsors given by an isomorphism of their
  stalks.
* `ContAction.nonabelianH1EquivStalk 𝒢`: the bijection `Sheaf.NonabelianH1 𝒢 ≃ H¹(G, A)`.

## Main results

* `ContAction.cls_torsorStalkSmoothTorsor_torsorOfSmoothTorsor`: the stalk of
  `torsorOfSmoothTorsor T` has the class of `T`.
* `ContAction.nonabelianH1ToStalk_injective`, `ContAction.nonabelianH1ToStalk_surjective`,
  `ContAction.nonabelianH1ToStalk_bijective`: taking stalks is a bijection from the classes of
  `𝒢`-torsors to `H¹(G, A)`.
-/

public section

open CategoryTheory Limits Opposite PreGaloisCategory FintypeCatDiscrete

universe u

namespace ContAction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {𝒢 : Sheaf (jointlySurjectiveTopology G) GrpCat.{u}}

section OfSmoothTorsor

variable (T : TauCeti.NonabelianH1.SmoothTorsor.{u, u, u} G ((point G).GrpStalk 𝒢.obj))

/-- The smooth `G`-set underlying a smooth torsor under the stalk of `𝒢`. -/
@[expose]
def smoothSetOfSmoothTorsor : Action.SmoothSet G :=
  ⟨Action.ofMulAction G T.carrier, (Action.isSmooth_iff _).2 T.isOpen_stabilizer⟩

/-- The `G`-set underlying `smoothSetOfSmoothTorsor T` is `T` with its action of `G`. -/
theorem smoothSetOfSmoothTorsor_obj :
    (smoothSetOfSmoothTorsor T).obj = Action.ofMulAction G T.carrier :=
  (rfl)

/-- A section `a` of `𝒢` over `S` acts on `G`-maps `φ : S → T` through its germs,
`(a • φ)(s) = [a]_s • φ(s)`. -/
noncomputable def torsorSMulHom {S : ContAction FintypeCat.{u} G} (a : 𝒢.obj.obj (op S))
    (φ : (fiberFunctor G).obj S →[G] T.carrier) : (fiberFunctor G).obj S →[G] T.carrier where
  toFun s := (point G).grpGerm 𝒢.obj S s a • φ s
  map_smul' g s := by
    dsimp only [id]
    rw [T.smul_distrib_smul, smul_grpGerm, map_smul]

/-- `torsorSMulHom T a φ` multiplies the value of `φ` at `s` by the germ of `a` at `s`. -/
theorem torsorSMulHom_apply {S : ContAction FintypeCat.{u} G} (a : 𝒢.obj.obj (op S))
    (φ : (fiberFunctor G).obj S →[G] T.carrier) (s : (fiberFunctor G).obj S) :
    torsorSMulHom T a φ s = (point G).grpGerm 𝒢.obj S s a • φ s :=
  (rfl)

/-- The sections of `𝒢` over `S` act on `G`-maps from `S` into a smooth torsor through their
germs. -/
@[implicit_reducible]
private noncomputable def torsorMulActionHom (S : ContAction FintypeCat.{u} G) :
    MulAction (𝒢.obj.obj (op S)) ((fiberFunctor G).obj S →[G] T.carrier) where
  smul a φ := torsorSMulHom T a φ
  -- The action being defined is `torsorSMulHom` by construction; `change` states the goals with
  -- it, so that `torsorSMulHom_apply` applies.
  one_smul φ := MulActionHom.ext fun s ↦ by
    change torsorSMulHom T 1 φ s = φ s
    rw [torsorSMulHom_apply, map_one, one_smul]
  mul_smul a b φ := MulActionHom.ext fun s ↦ by
    change torsorSMulHom T (a * b) φ s = torsorSMulHom T a (torsorSMulHom T b φ) s
    rw [torsorSMulHom_apply, torsorSMulHom_apply, torsorSMulHom_apply, map_mul, mul_smul]

/-- A section of the presheaf of `G`-maps into `T` is a `G`-map into `T`. -/
def sectionHom (S : ContAction FintypeCat.{u} G) :
    ((homPresheaf G).obj (Action.ofMulAction G T.carrier)).obj (op S) ≃
      ((fiberFunctor G).obj S →[G] T.carrier) :=
  (homPresheafObjEquiv _ S).trans
    { toFun φ := ⟨φ, φ.map_smul⟩
      invFun φ := ⟨φ, φ.map_smul⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- Restriction of `G`-maps into `T` is precomposition. -/
theorem sectionHom_map {S S' : ContAction FintypeCat.{u} G} (f : S' ⟶ S)
    (φ : ((homPresheaf G).obj (Action.ofMulAction G T.carrier)).obj (op S))
    (t : (fiberFunctor G).obj S') :
    sectionHom T S' (((homPresheaf G).obj (Action.ofMulAction G T.carrier)).map f.op φ) t =
      sectionHom T S φ ((fiberFunctor G).map f t) :=
  homPresheafObjEquiv_map _ f φ t

/-- The sections of `𝒢` over `S` act on the sections over `S` of the presheaf of `G`-maps into a
smooth torsor, through their germs. -/
@[implicit_reducible]
noncomputable def torsorMulAction (S : ContAction FintypeCat.{u} G) :
    MulAction (𝒢.obj.obj (op S))
      (((homPresheaf G).obj (Action.ofMulAction G T.carrier)).obj (op S)) :=
  @Equiv.mulAction _ _ _ _ (sectionHom T S) (torsorMulActionHom T S)

/-- A section of `𝒢` acts on a section of the presheaf of `G`-maps into `T` through its
germs. -/
theorem sectionHom_torsorSMul {S : ContAction FintypeCat.{u} G} (a : 𝒢.obj.obj (op S))
    (φ : ((homPresheaf G).obj (Action.ofMulAction G T.carrier)).obj (op S))
    (s : (fiberFunctor G).obj S) :
    sectionHom T S ((torsorMulAction T S).smul a φ) s =
      (point G).grpGerm 𝒢.obj S s a • sectionHom T S φ s :=
  congr($(Equiv.apply_symm_apply (sectionHom T S) (torsorSMulHom T a (sectionHom T S φ))) s)

/-- For `G`-maps `ψ, φ : S → T`, the `G`-map `s ↦ ψ(s) /ₛ φ(s)` from `S` into the stalk of
`𝒢`. -/
private noncomputable def torsorSDivHom {S : ContAction FintypeCat.{u} G}
    (ψ φ : (fiberFunctor G).obj S →[G] T.carrier) :
    (fiberFunctor G).obj S →[G] (point G).GrpStalk 𝒢.obj where
  toFun s := ψ s /ₛ φ s
  map_smul' g s := by
    dsimp only [id]
    rw [map_smul, map_smul, ← eq_smul_iff_sdiv_eq, ← T.smul_distrib_smul, sdiv_smul]

/-- The sections of `𝒢` act simply transitively on `G`-maps into a smooth torsor `T`. -/
theorem torsorMulAction_bijective (S : ContAction FintypeCat.{u} G) :
    Function.Bijective fun x : 𝒢.obj.obj (op S) ×
        ((homPresheaf G).obj (Action.ofMulAction G T.carrier)).obj (op S) ↦
      ((torsorMulAction T S).smul x.1 x.2, x.2) := by
  refine ⟨fun ⟨a, φ⟩ ⟨b, ψ⟩ h ↦ ?_, fun ⟨ψ, φ⟩ ↦ ?_⟩
  · obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 h
    refine Prod.ext (grpGerm_ext fun s ↦ smul_right_cancel (sectionHom T S φ s) ?_) rfl
    have := congr(sectionHom T S $h₁ s)
    rwa [sectionHom_torsorSMul, sectionHom_torsorSMul] at this
  · obtain ⟨a, ha⟩ := exists_grpGerm_eq S (torsorSDivHom T (sectionHom T S ψ) (sectionHom T S φ))
    refine ⟨(a, φ), Prod.ext ((sectionHom T S).injective (MulActionHom.ext fun s ↦ ?_)) rfl⟩
    rw [sectionHom_torsorSMul, ha]
    exact sdiv_smul _ _

/-- The action of the sections of `𝒢` on `G`-maps into `T` commutes with restriction. -/
theorem torsorSMul_map {S S' : ContAction FintypeCat.{u} G} (f : S' ⟶ S)
    (a : 𝒢.obj.obj (op S))
    (φ : ((homPresheaf G).obj (Action.ofMulAction G T.carrier)).obj (op S)) :
    ((homPresheaf G).obj (Action.ofMulAction G T.carrier)).map f.op
        ((torsorMulAction T S).smul a φ) =
      (torsorMulAction T S').smul (𝒢.obj.map f.op a)
        (((homPresheaf G).obj (Action.ofMulAction G T.carrier)).map f.op φ) := by
  refine (sectionHom T S').injective (MulActionHom.ext fun t ↦ ?_)
  rw [sectionHom_map, sectionHom_torsorSMul, sectionHom_torsorSMul, sectionHom_map,
    GrothendieckTopology.Point.grpGerm_map]

variable [CompactSpace G]

/-- The sheaf of `G`-maps into a smooth torsor `T` has sections locally: the objects over which it
has a section cover every object. -/
theorem coversTop_nonempty_homPresheaf :
    (jointlySurjectiveTopology G).CoversTop fun U : {U : ContAction FintypeCat.{u} G //
      Nonempty (((homPresheaf G).obj (Action.ofMulAction G T.carrier)).obj (op U))} ↦
        U.val := by
  intro S
  obtain ⟨t⟩ : Nonempty (smoothSetOfSmoothTorsor T).obj.V := (inferInstance : Nonempty T.carrier)
  have hX := (smoothSetOfSmoothTorsor T).property
  let O := orbitObj hX t
  refine mem_jointlySurjectiveTopology_iff.2 fun s ↦
    ⟨S ⨯ O, prod.fst, ⟨⟨S ⨯ O, ⟨(homPresheafObjEquiv _ _).symm
      ((orbitHom hX t).comp (fiberHom prod.snd))⟩⟩, ⟨𝟙 _⟩⟩,
      (fiberBinaryProductEquiv (forget₂ _ FintypeCat.{u}) S O).symm
        (s, ⟨t, MulAction.mem_orbit_self t⟩), ?_⟩
  exact fiberBinaryProductEquiv_symm_fst_apply (F := forget₂ _ FintypeCat.{u}) s _

/-- **The torsor of a smooth torsor**: for a smooth torsor `T` under the stalk of `𝒢`, the sheaf
of `G`-maps into `T`, on which a section `a` of `𝒢` acts by `(a • φ)(s) = [a]_s • φ(s)`. -/
@[expose]
noncomputable def torsorOfSmoothTorsor : Sheaf.Torsor 𝒢 where
  sheaf := (toSheaf G).obj (smoothSetOfSmoothTorsor T)
  mulAction U := torsorMulAction T U.unop
  map_smul _ _ f a φ := torsorSMul_map T f.unop a φ
  coversTop := coversTop_nonempty_homPresheaf T
  bijective U := torsorMulAction_bijective T U.unop

/-- The underlying sheaf of `torsorOfSmoothTorsor T` is the sheaf of `G`-maps into `T`. -/
theorem torsorOfSmoothTorsor_sheaf :
    (torsorOfSmoothTorsor T).sheaf = (toSheaf G).obj (smoothSetOfSmoothTorsor T) :=
  (rfl)

/-- Evaluation of germs from the stalk of `torsorOfSmoothTorsor T` to `T`. -/
noncomputable def evalTorsorStalk : (point G).TorsorStalk (torsorOfSmoothTorsor T) → T.carrier :=
  fun x ↦ evalStalk (Action.ofMulAction G T.carrier) x

/-- Evaluating the germ at `s` of a section `φ` gives `φ s`. -/
@[simp]
theorem evalTorsorStalk_toPresheafFiber (S : ContAction FintypeCat.{u} G)
    (s : (fiberFunctor G).obj S) (φ : (torsorOfSmoothTorsor T).sheaf.obj.obj (op S)) :
    evalTorsorStalk T ((point G).toPresheafFiber S s (torsorOfSmoothTorsor T).sheaf.obj φ) =
      sectionHom T S φ s :=
  evalStalk_germ _ S s φ

/-- Evaluation of germs from the stalk of `torsorOfSmoothTorsor T` to `T` commutes with the
action of `G`. -/
@[simp]
theorem evalTorsorStalk_smul_G (g : G) (x : (point G).TorsorStalk (torsorOfSmoothTorsor T)) :
    evalTorsorStalk T (g • x) = g • evalTorsorStalk T x :=
  evalStalk_smul _ g x

/-- Evaluation of germs from the stalk of `torsorOfSmoothTorsor T` to `T` commutes with the
action of the stalk of `𝒢`. -/
@[simp]
theorem evalTorsorStalk_smul_A (a : (point G).GrpStalk 𝒢.obj)
    (x : (point G).TorsorStalk (torsorOfSmoothTorsor T)) :
    evalTorsorStalk T (a • x) = a • evalTorsorStalk T x := by
  obtain ⟨S, s, b, φ, rfl, rfl⟩ :=
    (point G).exists_grpGerm_eq_toPresheafFiber_eq (torsorOfSmoothTorsor T) a x
  rw [GrothendieckTopology.Point.grpGerm_smul_toPresheafFiber, evalTorsorStalk_toPresheafFiber,
    evalTorsorStalk_toPresheafFiber]
  exact sectionHom_torsorSMul T b φ s

/-- **The stalk of `torsorOfSmoothTorsor T` has the class of `T`.** -/
theorem cls_torsorStalkSmoothTorsor_torsorOfSmoothTorsor
    [TopologicalSpace ((point G).GrpStalk 𝒢.obj)] :
    (torsorStalkSmoothTorsor (torsorOfSmoothTorsor T)).cls = T.cls :=
  TauCeti.NonabelianH1.SmoothTorsor.cls_eq_cls_of_map (evalTorsorStalk T)
    (evalTorsorStalk_smul_A T) (evalTorsorStalk_smul_G T)

end OfSmoothTorsor

section HomOfIso

variable {P Q : Sheaf.Torsor 𝒢}

/-- An isomorphism of the stalks of two torsors, as smooth torsors, is a morphism of smooth
`G`-sets between the stalks of their underlying sheaves of sets. -/
noncomputable def smoothSetHomOfIso
    (e : (torsorStalkSmoothTorsor P).Iso (torsorStalkSmoothTorsor Q)) :
    (fromSheaf G).obj P.sheaf ⟶ (fromSheaf G).obj Q.sheaf :=
  ObjectProperty.homMk
    { hom := TypeCat.ofHom e.toEquiv
      comm g := by
        ext x
        exact e.map_smul_G g x }

/-- `smoothSetHomOfIso e` is `e` on stalks. -/
theorem smoothSetHomOfIso_hom_apply
    (e : (torsorStalkSmoothTorsor P).Iso (torsorStalkSmoothTorsor Q))
    (x : (point G).TorsorStalk P) :
    (smoothSetHomOfIso e).hom.hom x = e.toEquiv x :=
  (rfl)

variable [CompactSpace G]

/-- The morphism of sheaves of sets underlying `torsorHomOfIso e`: the morphism whose map of
stalks is `e`. -/
noncomputable def sheafHomOfIso
    (e : (torsorStalkSmoothTorsor P).Iso (torsorStalkSmoothTorsor Q)) : P.sheaf ⟶ Q.sheaf :=
  (fromSheafFullyFaithful G).preimage (smoothSetHomOfIso e)

/-- The map of stalks induced by `sheafHomOfIso e` is `e`. -/
@[simp]
theorem presheafFiber_map_sheafHomOfIso
    (e : (torsorStalkSmoothTorsor P).Iso (torsorStalkSmoothTorsor Q))
    (x : (point G).TorsorStalk P) :
    (point G).presheafFiber.map (sheafHomOfIso e).hom x = e.toEquiv x := by
  have := (fromSheafFullyFaithful G).map_preimage (smoothSetHomOfIso e)
  exact congr(($this).hom.hom x)

/-- **An isomorphism of stalks gives a morphism of torsors**: the morphism of `𝒢`-torsors whose
map of stalks is `e`. -/
noncomputable def torsorHomOfIso
    (e : (torsorStalkSmoothTorsor P).Iso (torsorStalkSmoothTorsor Q)) : P ⟶ Q where
  hom := sheafHomOfIso e
  map_smul U a p := germ_ext Q.sheaf fun s ↦ by
    dsimp only [germ]
    rw [← GrothendieckTopology.Point.grpGerm_smul_toPresheafFiber,
      ← GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
      ← GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
      presheafFiber_map_sheafHomOfIso, presheafFiber_map_sheafHomOfIso,
      ← GrothendieckTopology.Point.grpGerm_smul_toPresheafFiber]
    exact e.map_smul_A _ _

/-- The morphism of sheaves underlying `torsorHomOfIso e` is `sheafHomOfIso e`. -/
@[simp]
theorem torsorHomOfIso_hom
    (e : (torsorStalkSmoothTorsor P).Iso (torsorStalkSmoothTorsor Q)) :
    (torsorHomOfIso e).hom = sheafHomOfIso e :=
  (rfl)

end HomOfIso

section Bijective

variable [CompactSpace G] [TopologicalSpace ((point G).GrpStalk 𝒢.obj)]

variable (𝒢) in
/-- Taking stalks is injective on the classes of `𝒢`-torsors: torsors whose stalks are
isomorphic smooth torsors are isomorphic. -/
theorem nonabelianH1ToStalk_injective : Function.Injective (nonabelianH1ToStalk 𝒢) := by
  intro x y h
  induction x using Sheaf.NonabelianH1.ind with | h P => ?_
  induction y using Sheaf.NonabelianH1.ind with | h Q => ?_
  rw [nonabelianH1ToStalk_mk, nonabelianH1ToStalk_mk,
    TauCeti.NonabelianH1.SmoothTorsor.cls_eq_cls_iff] at h
  obtain ⟨e⟩ := h
  exact Sheaf.NonabelianH1.mk_eq_mk_of_hom (torsorHomOfIso e)

variable [DiscreteTopology ((point G).GrpStalk 𝒢.obj)]

variable (𝒢) in
/-- Taking stalks is surjective onto `H¹(G, A)`, `A` the stalk of `𝒢` with the discrete
topology. -/
theorem nonabelianH1ToStalk_surjective : Function.Surjective (nonabelianH1ToStalk 𝒢) := by
  have : ContinuousSMul G ((point G).GrpStalk 𝒢.obj) :=
    continuousSMul_iff_stabilizer_isOpen.2 (isOpen_stabilizer_grpStalk 𝒢.obj)
  intro c
  obtain ⟨T, rfl⟩ := TauCeti.NonabelianH1.SmoothTorsor.cls_surjective c
  exact ⟨Sheaf.NonabelianH1.mk (torsorOfSmoothTorsor T), by
    rw [nonabelianH1ToStalk_mk, cls_torsorStalkSmoothTorsor_torsorOfSmoothTorsor]⟩

variable (𝒢) in
/-- **Torsors under a sheaf of groups on finite continuous `G`-sets are classified by continuous
nonabelian `H¹`.** For compact `G`, taking stalks is a bijection from the classes of `𝒢`-torsors
to `H¹(G, A)`, with `A` the stalk of `𝒢` with the discrete topology. -/
theorem nonabelianH1ToStalk_bijective : Function.Bijective (nonabelianH1ToStalk 𝒢) :=
  ⟨nonabelianH1ToStalk_injective 𝒢, nonabelianH1ToStalk_surjective 𝒢⟩

variable (𝒢) in
/-- The bijection `Sheaf.NonabelianH1 𝒢 ≃ H¹(G, A)` given by taking stalks, for compact `G`
and `A` the stalk of `𝒢` with the discrete topology. -/
noncomputable def nonabelianH1EquivStalk :
    Sheaf.NonabelianH1 𝒢 ≃ TauCeti.NonabelianH1 G ((point G).GrpStalk 𝒢.obj) :=
  Equiv.ofBijective _ (nonabelianH1ToStalk_bijective 𝒢)

/-- `nonabelianH1EquivStalk 𝒢` sends the class of a torsor to the class of its stalk. -/
@[simp]
theorem nonabelianH1EquivStalk_mk (P : Sheaf.Torsor 𝒢) :
    nonabelianH1EquivStalk 𝒢 (Sheaf.NonabelianH1.mk P) = (torsorStalkSmoothTorsor P).cls :=
  nonabelianH1ToStalk_mk P

/-- The inverse of `nonabelianH1EquivStalk 𝒢` sends the class of a smooth torsor `T` to the class
of the torsor of `G`-maps into `T`. -/
@[simp]
theorem nonabelianH1EquivStalk_symm_cls
    (T : TauCeti.NonabelianH1.SmoothTorsor.{u, u, u} G ((point G).GrpStalk 𝒢.obj)) :
    (nonabelianH1EquivStalk 𝒢).symm T.cls = Sheaf.NonabelianH1.mk (torsorOfSmoothTorsor T) := by
  rw [Equiv.symm_apply_eq, nonabelianH1EquivStalk_mk,
    cls_torsorStalkSmoothTorsor_torsorOfSmoothTorsor]

end Bijective

end ContAction
