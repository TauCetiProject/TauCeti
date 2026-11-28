/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.CoordinateIso

/-!
# Chosen split maximal tori over a ring

`SplitMaximalTorus R H r` is a closed immersion of the standard rank-`r` split torus into
the affine group with coordinate algebra `H`, maximal on every geometric fiber. It carries
the coordinate morphism itself, rather than an existence assertion. The corresponding Hopf
ideal and its quotient presentation are recovered from that morphism.

Maximality on geometric fibers is essential: maximality merely among tori over the base
does not imply this condition. A chosen split maximal torus does not include a pinning or
trivializations of the root spaces over the base.

Chosen split maximal tori are transported along isomorphisms of coordinate Hopf algebras
(`SplitMaximalTorus.comapOfIso`) and base-changed along ring maps `R → S`
(`SplitMaximalTorus.baseChange`). The base-changed torus is cut out by the base change of the
original defining ideal, and its geometric fibers are geometric fibers of the original torus, so
a torus chosen over `ℤ` specializes to every commutative ring.

## Main declarations

* `TauCeti.SplitMaximalTorus`: a chosen split maximal torus of an affine group over a ring.
* `TauCeti.SplitMaximalTorus.ofSurjective`: construction from a surjective map in unlifted
  finite-rank coordinates and geometric-fiber maximality of its kernel.
* `TauCeti.SplitMaximalTorus.comapOfIso`: transport along an isomorphism of coordinate Hopf
  algebras.
* `TauCeti.SplitMaximalTorus.baseChange`: base change along `R → S`.
* `TauCeti.SplitMaximalTorus.baseChange_coordinateMap_hom_one_tmul`: the base-changed torus
  restricts `1 ⊗ h` to the coefficient image of the restriction of `h`.
* `TauCeti.SplitMaximalTorus.definingIdeal_baseChange`: the base-changed torus is cut out by the
  base change of the defining ideal.
* `TauCeti.SplitMaximalTorus.comapOfIso_baseChange_self`, `baseChange_baseChange` and
  `baseChange_comapOfIso`: base change of tori is trivial along the identity, composes in stages
  and commutes with transport along isomorphisms.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.2.1 and Example 3.2.3.
* The unlifted-coordinate constructor abstracts the construction in
  `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.MaximalTorus`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- A parametrized split maximal torus of an affine group over `R`. The coordinate map is
surjective, expressing a closed immersion, and its defining ideal is maximal as a torus
on every geometric fiber. -/
structure SplitMaximalTorus (R : Type u) [CommRing R]
    (H : CommHopfAlgCat.{u} R) [Algebra.FiniteType R H] (r : ℕ) where
  /-- Restriction of functions to the chosen rank-`r` split torus. -/
  coordinateMap : H ⟶
    (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin r)))).obj
  /-- The chosen torus is a closed subgroup. -/
  surjective : Function.Surjective coordinateMap.hom
  /-- The chosen torus is maximal in every geometric fiber. -/
  maximal : ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k)
        (HopfIdeal.kerOfSurjective coordinateMap.hom surjective))

namespace SplitMaximalTorus

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R}
    [Algebra.FiniteType R H] {r : ℕ}

/-- A chosen split maximal torus is determined by its coordinate map. -/
@[ext]
theorem ext {T U : SplitMaximalTorus R H r} (h : T.coordinateMap = U.coordinateMap) : T = U := by
  cases T
  cases U
  cases h
  rfl

/-- The Hopf ideal cutting out the chosen split maximal torus. -/
noncomputable def definingIdeal (T : SplitMaximalTorus R H r) : HopfIdeal R H :=
  HopfIdeal.kerOfSurjective T.coordinateMap.hom T.surjective

/-- A function belongs to the defining ideal exactly when its restriction to the torus is zero. -/
@[simp]
theorem mem_definingIdeal (T : SplitMaximalTorus R H r) (x : H) :
    x ∈ T.definingIdeal ↔ T.coordinateMap.hom x = 0 :=
  HopfIdeal.mem_kerOfSurjective T.coordinateMap.hom T.surjective

/-- The quotient coordinate algebra of the chosen torus is the standard split-torus algebra. -/
noncomputable def coordinateIso (T : SplitMaximalTorus R H r) :
    FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of R H) T.definingIdeal ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin r))) :=
  ObjectProperty.isoMk _
    (CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso T.coordinateMap T.surjective)

/-- The quotient presentation recovers restriction to the torus. -/
@[simp]
theorem mkQuotient_comp_coordinateIso_hom (T : SplitMaximalTorus R H r) :
    FiniteTypeCommHopfAlgCat.mkQuotient (FiniteTypeCommHopfAlgCat.of R H) T.definingIdeal ≫
        T.coordinateIso.hom =
      ObjectProperty.homMk T.coordinateMap :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The closed subgroup defined by the chosen torus is a split torus over the base ring. -/
theorem splitTorus_quotient (T : SplitMaximalTorus R H r) :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of R H) T.definingIdeal) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨r, ⟨T.coordinateIso.symm⟩⟩

/-- The chosen torus is maximal after extension to any algebraically closed field over `R`. -/
theorem isMaximalTorus_geometricFiber (T : SplitMaximalTorus R H r)
    (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k] :
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k) T.definingIdeal) :=
  T.maximal k

section OfSurjective

variable (π : H ⟶ (DiagonalizableGroup.coordinateRing R
    (SplitTorus.characterGroup (Fin r))).obj) (hπ : Function.Surjective π.hom)

omit [Algebra.FiniteType R H] in
/-- Reindexing finite-rank coordinates by universe lifting preserves the kernel. -/
private theorem kerOfSurjective_comp_uliftCoordinateRingIso
    (hs : Function.Surjective (π ≫ (SplitTorus.uliftCoordinateRingIso R r).hom).hom) :
    HopfIdeal.kerOfSurjective _ hs = HopfIdeal.kerOfSurjective π.hom hπ := by
  ext x
  simp only [HopfIdeal.mem_kerOfSurjective, CommHopfAlgCat.hom_comp,
    BialgHom.coe_comp, Function.comp_apply]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (SplitTorus.uliftCoordinateRingIso R r).hom).1

/-- Construct a chosen split maximal torus from a surjective coordinate map in unlifted
finite-rank coordinates and maximality of its kernel on every geometric fiber. -/
noncomputable def ofSurjective
    (hmax : ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
      HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) H)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := k) (HopfIdeal.kerOfSurjective π.hom hπ))) :
    SplitMaximalTorus R H r where
  coordinateMap := π ≫ (SplitTorus.uliftCoordinateRingIso R r).hom
  surjective := by
    rw [CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp hπ
  maximal := by
    intro k _ _ _
    rw [kerOfSurjective_comp_uliftCoordinateRingIso π hπ]
    exact hmax k

variable (hmax : ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k) (HopfIdeal.kerOfSurjective π.hom hπ)))

/-- The coordinate map of `ofSurjective` is the original map followed by universe lifting. -/
@[simp]
theorem ofSurjective_coordinateMap :
    (ofSurjective π hπ hmax).coordinateMap =
      π ≫ (SplitTorus.uliftCoordinateRingIso R r).hom :=
  (rfl)

/-- Reindexing the torus coordinates does not change the defining kernel. -/
@[simp]
theorem definingIdeal_ofSurjective :
    (ofSurjective π hπ hmax).definingIdeal = HopfIdeal.kerOfSurjective π.hom hπ :=
  kerOfSurjective_comp_uliftCoordinateRingIso π hπ (ofSurjective π hπ hmax).surjective

end OfSurjective

section ComapOfIso

variable {L : CommHopfAlgCat.{u} R} [Algebra.FiniteType R L]

/-- Transport of a chosen split maximal torus across an isomorphism `e : H ≅ L` of coordinate
Hopf algebras: the torus of `L` becomes a torus of `H` by restricting functions along `e`. -/
noncomputable def comapOfIso (T : SplitMaximalTorus R L r) (e : H ≅ L) :
    SplitMaximalTorus R H r where
  coordinateMap := e.hom ≫ T.coordinateMap
  surjective := by
    rw [CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact T.surjective.comp (ConcreteCategory.bijective_of_isIso e.hom).2
  maximal := by
    intro k _ _ _
    have hker (hs : Function.Surjective (e.hom ≫ T.coordinateMap).hom) :
        HopfIdeal.kerOfSurjective _ hs = T.definingIdeal.comapOfSurjective e.hom.hom
          (ConcreteCategory.bijective_of_isIso e.hom).2 := by
      ext x
      simp [definingIdeal]
    let ek : FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.baseChange (K := k) H) ≅
        FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.baseChange (K := k) L) :=
      ObjectProperty.isoMk _ ((CommHopfAlgCat.baseChangeFunctor (K := k)).mapIso e)
    rw [hker, CommHopfAlgCat.baseChangeHopfIdeal_comapOfIso]
    exact (T.isMaximalTorus_geometricFiber k).comapOfIso ek

/-- The transported torus has coordinate map `e.hom ≫ T.coordinateMap`. -/
@[simp]
theorem comapOfIso_coordinateMap (T : SplitMaximalTorus R L r) (e : H ≅ L) :
    (T.comapOfIso e).coordinateMap = e.hom ≫ T.coordinateMap :=
  (rfl)

/-- The coordinate map of a transported torus is restriction along the bialgebra equivalence
underlying the isomorphism. -/
theorem hom_comapOfIso_coordinateMap (T : SplitMaximalTorus R L r) (e : H ≅ L) :
    (T.comapOfIso e).coordinateMap.hom =
      T.coordinateMap.hom.comp (CommHopfAlgCat.ofIso e : H →ₐc[R] L) := by
  rw [comapOfIso_coordinateMap, CommHopfAlgCat.hom_comp, CommHopfAlgCat.coe_ofIso]

/-- The defining ideal of the transported torus is the pullback of the original defining ideal
along `e`. -/
@[simp]
theorem definingIdeal_comapOfIso (T : SplitMaximalTorus R L r) (e : H ≅ L) :
    (T.comapOfIso e).definingIdeal =
      T.definingIdeal.comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 := by
  ext x
  simp

end ComapOfIso

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The coordinate map of the base-changed torus cuts out the base change of the defining
ideal. -/
private theorem kerOfSurjective_baseChangeMap_comp (T : SplitMaximalTorus R H r)
    (hT : Function.Surjective (CommHopfAlgCat.baseChangeMap (K := S) T.coordinateMap ≫
      (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R S
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))).hom).hom) :
    HopfIdeal.kerOfSurjective _ hT = CommHopfAlgCat.baseChangeHopfIdeal (K := S) T.definingIdeal :=
  ((HopfIdeal.map_id _).symm.trans
    (CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective (Iso.refl _)
      (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R S
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))) T.surjective hT
      (by rw [Iso.refl_inv, Category.id_comp]))).symm

/-- **Base change of a chosen split maximal torus** along `R → S`. Its coordinate map is the
base change of the original one, read in the standard split-torus coordinates over `S`; its
geometric fibers are geometric fibers of the original torus. -/
noncomputable def baseChange (T : SplitMaximalTorus R H r) :
    SplitMaximalTorus S (CommHopfAlgCat.baseChange (K := S) H) r where
  coordinateMap := CommHopfAlgCat.baseChangeMap (K := S) T.coordinateMap ≫
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R S
      (SplitTorus.characterGroup (ULift.{u} (Fin r)))).hom
  surjective := by
    rw [CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp
      (CommHopfAlgCat.baseChangeMap_surjective _ T.surjective)
  maximal := by
    intro k _ _ _
    let _ : Algebra R k := ((algebraMap S k).comp (algebraMap R S)).toAlgebra
    let _ : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let e := FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := S) R k
      ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
    rw [kerOfSurjective_baseChangeMap_comp, CommHopfAlgCat.baseChangeHopfIdeal_baseChangeHopfIdeal]
    simpa only [e, FiniteTypeCommHopfAlgCat.toBialgHom,
      FiniteTypeCommHopfAlgCat.baseChangeTowerIso_hom_hom] using
      (T.isMaximalTorus_geometricFiber k).comapOfIso e

/-- The base-changed torus has the base-changed coordinate map. -/
@[simp]
theorem baseChange_coordinateMap (T : SplitMaximalTorus R H r) :
    (T.baseChange S).coordinateMap =
      CommHopfAlgCat.baseChangeMap (K := S) T.coordinateMap ≫
        (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R S
          (SplitTorus.characterGroup (ULift.{u} (Fin r)))).hom :=
  (rfl)

/-- The base-changed torus restricts `1 ⊗ h` to the restriction of `h` to the original torus,
with its coefficients mapped along `R → S`. -/
theorem baseChange_coordinateMap_hom_one_tmul (T : SplitMaximalTorus R H r) (h : H) :
    (T.baseChange S).coordinateMap.hom (1 ⊗ₜ h) =
      MonoidAlgebra.mapAlgHom _ (Algebra.ofId R S) (T.coordinateMap.hom h) := by
  rw [baseChange_coordinateMap, CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    CommHopfAlgCat.baseChangeMap_apply_tmul,
    DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso_hom_apply,
    MonoidAlgebra.scalarTensorBialgEquiv_tmul, one_smul]

/-- The defining ideal of the base-changed torus is the base change of the defining ideal. -/
@[simp]
theorem definingIdeal_baseChange (T : SplitMaximalTorus R H r) :
    (T.baseChange S).definingIdeal =
      CommHopfAlgCat.baseChangeHopfIdeal (K := S) T.definingIdeal :=
  kerOfSurjective_baseChangeMap_comp S T (T.baseChange S).surjective

/-- **Base change along the identity is trivial**: the base change of a torus along `R → R`,
transported along `H ≅ R ⊗[R] H`, is the original torus. -/
@[simp]
theorem comapOfIso_baseChange_self (T : SplitMaximalTorus R H r) :
    (T.baseChange R).comapOfIso (CommHopfAlgCat.baseChangeSelfIso H).symm = T := by
  ext1
  ext h : 2
  rw [comapOfIso_coordinateMap, CommHopfAlgCat.hom_comp, BialgHom.comp_apply, Iso.symm_hom,
    CommHopfAlgCat.baseChangeSelfIso_inv_apply, baseChange_coordinateMap_hom_one_tmul,
    Algebra.ofId_self, MonoidAlgebra.mapAlgHom_id, AlgHom.id_apply]

/-- **Base change of tori composes in stages**: for a tower `R → S → S'`, base-changing a torus to
`S` and then to `S'` gives its base change to `S'`, transported along the tower identification
`S' ⊗[S] (S ⊗[R] H) ≅ S' ⊗[R] H`. -/
theorem baseChange_baseChange (S' : Type u) [CommRing S'] [Algebra R S'] [Algebra S S']
    [IsScalarTower R S S'] (T : SplitMaximalTorus R H r) :
    (T.baseChange S).baseChange S' =
      (T.baseChange S').comapOfIso (CommHopfAlgCat.baseChangeTowerIso R S' H) := by
  ext1
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  -- An `S'`-algebra map out of `S' ⊗[S] (S ⊗[R] H)` is determined by the elements `1 ⊗ (1 ⊗ h)`.
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _)
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun h ↦ ?_))
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, BialgHom.coe_toAlgHom]
  rw [baseChange_coordinateMap_hom_one_tmul, comapOfIso_coordinateMap, CommHopfAlgCat.hom_comp,
    BialgHom.comp_apply, CommHopfAlgCat.baseChangeTowerIso_hom_apply, one_smul,
    baseChange_coordinateMap_hom_one_tmul, baseChange_coordinateMap_hom_one_tmul]
  ext m
  simp only [MonoidAlgebra.coeff_mapAlgHom, Algebra.ofId_apply,
    IsScalarTower.algebraMap_apply R S S']

variable {L : CommHopfAlgCat.{u} R} [Algebra.FiniteType R L]

/-- **Base change commutes with transport along isomorphisms**: base-changing a torus transported
along `e : H ≅ L` gives the transport of the base-changed torus along the base change of `e`. -/
theorem baseChange_comapOfIso (T : SplitMaximalTorus R L r) (e : H ≅ L) :
    (T.comapOfIso e).baseChange S =
      (T.baseChange S).comapOfIso ((CommHopfAlgCat.baseChangeFunctor (K := S)).mapIso e) := by
  ext1
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  -- An `S`-algebra map out of `S ⊗[R] H` is determined by the elements `1 ⊗ h`.
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun h ↦ ?_)
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, BialgHom.coe_toAlgHom]
  rw [baseChange_coordinateMap_hom_one_tmul, comapOfIso_coordinateMap, comapOfIso_coordinateMap,
    Functor.mapIso_hom, CommHopfAlgCat.baseChangeFunctor_map]
  simp only [CommHopfAlgCat.hom_comp, BialgHom.comp_apply]
  rw [CommHopfAlgCat.baseChangeMap_apply_tmul, baseChange_coordinateMap_hom_one_tmul]

end BaseChange

end SplitMaximalTorus

end TauCeti
