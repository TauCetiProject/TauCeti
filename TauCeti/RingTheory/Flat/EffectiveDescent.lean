/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import TauCeti.RingTheory.TensorProduct.IsBaseChange
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Effective faithfully flat descent for algebras

Let `S` be an `R`-algebra. A descent datum on an `S`-algebra `B` relative to `R → S` is recorded
as an `S`-algebra map `θ : B → S ⊗[R] B` (the *coaction*) which is a section of the
multiplication map `S ⊗[R] B → B` and satisfies the coassociativity condition
`(id ⊗ θ) ∘ θ = (id ⊗ (1 ⊗ ·)) ∘ θ` in `S ⊗[R] (S ⊗[R] B)`. This is the classical
isomorphism-plus-cocycle formulation in another guise: an isomorphism of
`S ⊗[R] S`-algebras `φ : B ⊗[R] S ≅ S ⊗[R] B` corresponds to `θ b = φ (b ⊗ 1)`, the
normalisation of `φ` on the diagonal to the counit equation, and the cocycle condition on
`S ⊗[R] S ⊗[R] S` to coassociativity. Forgetting the multiplication, a descent datum is in
particular a coalgebra for the comonad `S ⊗[R] -` on `S`-modules (the module form of descent,
behind Mathlib's `comonadicExtendScalars`); the algebra structure adds the requirement that the
coaction be an `S`-algebra map.

Since `Spec` is an anti-equivalence between commutative `R`-algebras and affine schemes over
`Spec R`, the results below are effective descent for affine schemes along a faithfully flat
morphism `Spec S → Spec R` of affine schemes:

* `TauCeti.Algebra.DescentDatum.baseChangeEquiv` (effectivity): if `S` is flat over `R`, the
  descended algebra `D.descended = {b | θ b = 1 ⊗ b}` satisfies `S ⊗[R] D.descended ≃ B`, and
  `coaction_baseChangeEquiv` identifies `θ` with the canonical datum on `S ⊗[R] D.descended`.
* `TauCeti.Algebra.DescentDatum.descended_baseChange`: if `S` is faithfully flat over `R`, the
  canonical datum on `S ⊗[R] A` descends to (the image of) `A`.
* `TauCeti.Algebra.DescentDatum.equivDescended` (uniqueness): if `S` is faithfully flat over `R`,
  every `R`-algebra `A` with `S ⊗[R] A ≃ B` compatibly with the descent data is isomorphic to
  `D.descended`.

Morphisms of descent data (`TauCeti.Algebra.DescentDatum.Hom`, `S`-algebra maps intertwining the
coactions) descend as well. Together with effectivity, this says that `A ↦ baseChange R S A` from
`R`-algebras to algebras with descent data is fully faithful and essentially surjective when `S`
is faithfully flat over `R`:

* `TauCeti.Algebra.DescentDatum.homEquiv` (descent of morphisms): if `S` is flat over `R`,
  morphisms of descent data `D → D'` correspond to `R`-algebra maps
  `D.descended → D'.descended`, compatibly with identities and composition (`Hom.descend_id`,
  `Hom.descend_comp`) and with `baseChangeEquiv` (`Hom.toAlgHom_baseChangeEquiv`).
* `TauCeti.Algebra.DescentDatum.baseChangeHomEquiv` (full faithfulness): if `S` is faithfully
  flat over `R`, the `R`-algebra maps `A → A'` are exactly the morphisms between the canonical
  descent data on `S ⊗[R] A` and `S ⊗[R] A'`.

Forming the descended algebra commutes with arbitrary base change `R → R'`:

* `TauCeti.Algebra.DescentDatum.exact_lTensor_descended_val` and
  `lTensor_descended_val_injective`: if `S` is faithfully flat over `R`, then
  `M ⊗[R] D.descended → M ⊗[R] B ⇉ M ⊗[R] (S ⊗[R] B)` is an equalizer for every `R`-module `M`.
* `TauCeti.Algebra.DescentDatum.tensorDescendedEquiv`: if `S` is faithfully flat over `R` and a
  descent datum `D'` on `B'` relative to `R' → S'` is the base change of `D` along `R → R'`
  (that is, `S' = R' ⊗[R] S` and `B' = R' ⊗[R] B` compatibly with the coactions), then
  `R' ⊗[R] D.descended ≃ D'.descended`. This is the compatibility on overlaps needed to glue
  the descents over the affine opens of a non-affine base.

The faithfully flat input is the exactness of the Amitsur sequence
`M → S ⊗[R] M ⇉ S ⊗[R] (S ⊗[R] M)` for an arbitrary `R`-module `M`
(`Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one`), which generalises Mathlib's
`Algebra.IsEffective.of_faithfullyFlat` (the case `M = R`, after identifying `S ⊗[R] R` with
`S`).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1 (effective descent for affine morphisms along faithfully flat quasi-compact
  morphisms).
* The Stacks Project, Chapter *Descent*, Section *Descent for modules* (the Amitsur complex
  argument used here).
-/

public section

open TensorProduct

section Amitsur

variable {R : Type*} (S : Type*) (M : Type*) [CommRing R] [Ring S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- **Amitsur exactness.** If `S` is a faithfully flat `R`-algebra, then for every `R`-module
`M` the sequence `M → S ⊗[R] M → S ⊗[R] (S ⊗[R] M)`, with maps `m ↦ 1 ⊗ m` and
`s ⊗ m ↦ s ⊗ (1 ⊗ m) - 1 ⊗ (s ⊗ m)`, is exact. -/
theorem Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one [Module.FaithfullyFlat R S] :
    Function.Exact (TensorProduct.mk R S M 1)
      ((TensorProduct.mk R S M 1).lTensor S - TensorProduct.mk R S (S ⊗[R] M) 1) := by
  set d := (TensorProduct.mk R S M 1).lTensor S - TensorProduct.mk R S (S ⊗[R] M) 1
  have hd : d ∘ₗ TensorProduct.mk R S M 1 = 0 := by
    ext m
    simp [d]
  -- After base change to `S`, the action `s ⊗ x ↦ s • x` of `S` on the left factor (multiplying
  -- the first two factors) is a contracting homotopy.
  let h := TensorProduct.lift (Algebra.lsmul R R (A := S) (S ⊗[R] M)).toLinearMap
  let h' := TensorProduct.lift (Algebra.lsmul R R (A := S) (S ⊗[R] (S ⊗[R] M))).toLinearMap
  have key : h' ∘ₗ d.lTensor S = (TensorProduct.mk R S M 1).lTensor S ∘ₗ h - LinearMap.id := by
    ext s t m
    simp [d, h, h', smul_tmul']
  refine Module.FaithfullyFlat.lTensor_reflects_exact R S _ _ fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · refine ⟨h y, ?_⟩
    have := congr($key y)
    simp only [LinearMap.comp_apply, hy, map_zero, LinearMap.sub_apply, LinearMap.id_apply] at this
    exact (sub_eq_zero.mp this.symm)
  · rintro ⟨x, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hd, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

end Amitsur

namespace TauCeti

namespace Algebra

variable (R S B : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Ring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- A descent datum on the `S`-algebra `B` relative to `R → S`, in coalgebra form: an
`S`-algebra map `coaction : B → S ⊗[R] B` (where `S` acts on the left factor) which is a section
of the multiplication map `s ⊗ b ↦ s • b` and is coassociative. In terms of the classical
gluing isomorphism `φ : B ⊗[R] S ≅ S ⊗[R] B` one has `coaction b = φ (b ⊗ 1)`;
`counit_coaction` is the normalisation of `φ` and `coassoc` is the cocycle condition. -/
@[ext]
structure DescentDatum where
  /-- The coaction `B → S ⊗[R] B`, linear over `S` acting on the left factor. -/
  coaction : B →ₐ[S] S ⊗[R] B
  /-- The coaction is a section of the multiplication map `S ⊗[R] B → B`. -/
  counit_coaction (b : B) :
    Algebra.TensorProduct.lift (Algebra.ofId S B) (AlgHom.id R B)
      (fun s b ↦ by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left s _)
      (coaction b) = b
  /-- The cocycle condition: `(id ⊗ θ) ∘ θ = (id ⊗ (1 ⊗ ·)) ∘ θ`. -/
  coassoc (b : B) :
    Algebra.TensorProduct.map (AlgHom.id R S) (coaction.restrictScalars R) (coaction b) =
      Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight (coaction b)

namespace DescentDatum

variable {R S B} (D : DescentDatum R S B)

/-- The coaction of a descent datum is injective, being a section of the multiplication map. -/
theorem coaction_injective : Function.Injective D.coaction :=
  Function.LeftInverse.injective D.counit_coaction

/-- The algebra descended from a descent datum: the `R`-subalgebra of elements `b` with
`coaction b = 1 ⊗ b`. -/
def descended : Subalgebra R B :=
  AlgHom.equalizer (D.coaction.restrictScalars R) Algebra.TensorProduct.includeRight

@[simp]
theorem mem_descended_iff {b : B} : b ∈ D.descended ↔ D.coaction b = 1 ⊗ₜ b :=
  Iff.rfl

/-- The comparison map `S ⊗[R] D.descended → B`, `s ⊗ a ↦ s • a`. -/
private noncomputable def baseChangeHom : S ⊗[R] D.descended →ₐ[S] B :=
  Algebra.TensorProduct.lift (Algebra.ofId S B) D.descended.val fun s a ↦ by
    rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left s _

private theorem coaction_baseChangeHom (x : S ⊗[R] D.descended) :
    D.coaction (D.baseChangeHom x) =
      Algebra.TensorProduct.map (AlgHom.id R S) D.descended.val x := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    have ha : D.coaction a = 1 ⊗ₜ (a : B) := a.2
    rw [baseChangeHom, Algebra.TensorProduct.lift_tmul]
    simp [ha, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [hx, hy]

private theorem baseChangeHom_bijective [Module.Flat R S] :
    Function.Bijective D.baseChangeHom := by
  have hθ : ∀ x : S ⊗[R] D.descended,
      D.coaction (D.baseChangeHom x) = (D.descended.val.toLinearMap).lTensor S x :=
    fun x ↦ by rw [coaction_baseChangeHom, AlgHom.lTensor_toLinearMap_apply]
  refine ⟨fun x y hxy ↦ ?_, fun b ↦ ?_⟩
  · refine Module.Flat.lTensor_preserves_injective_linearMap D.descended.val.toLinearMap
      (fun _ _ h ↦ Subtype.ext h) ?_
    rw [← hθ, ← hθ, hxy]
  -- The coaction of `b` is killed by the base change of the equalizer pair, by coassociativity.
  have hexact : Function.Exact D.descended.val.toLinearMap
      ((D.coaction.restrictScalars R).toLinearMap -
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toLinearMap) := fun b ↦
    ⟨fun h ↦ ⟨⟨b, sub_eq_zero.mp h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact sub_eq_zero.mpr a.2⟩
  obtain ⟨x, hx⟩ := ((Module.Flat.lTensor_exact S hexact) (D.coaction b)).mp <| by
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, AlgHom.lTensor_toLinearMap_apply,
      AlgHom.lTensor_toLinearMap_apply, D.coassoc, sub_self]
  exact ⟨x, D.coaction_injective (by rw [hθ, hx])⟩

/-- **Effectivity of flat descent for algebras.** If `S` is flat over `R`, every descent datum
on `B` is effective: the descended algebra base changes back to `B`, via `s ⊗ a ↦ s • a`. -/
noncomputable def baseChangeEquiv [Module.Flat R S] : S ⊗[R] D.descended ≃ₐ[S] B :=
  AlgEquiv.ofBijective D.baseChangeHom D.baseChangeHom_bijective

@[simp]
theorem baseChangeEquiv_tmul [Module.Flat R S] (s : S) (a : D.descended) :
    D.baseChangeEquiv (s ⊗ₜ a) = s • (a : B) := by
  simp [baseChangeEquiv, baseChangeHom, Algebra.smul_def]

/-- `baseChangeEquiv` is compatible with the descent data: the coaction of `D` sends
`s • a`, for `a` in the descended algebra, to `s ⊗ a`. Equivalently, `baseChangeEquiv`
carries the canonical descent datum `s ⊗ a ↦ s ⊗ (1 ⊗ a)` on `S ⊗[R] D.descended` to `D`. -/
theorem coaction_baseChangeEquiv [Module.Flat R S] (x : S ⊗[R] D.descended) :
    D.coaction (D.baseChangeEquiv x) =
      Algebra.TensorProduct.map (AlgHom.id R S) D.descended.val x :=
  D.coaction_baseChangeHom x

variable (R S) in
/-- The canonical descent datum on `S ⊗[R] A`, with coaction `s ⊗ a ↦ s ⊗ (1 ⊗ a)`. -/
noncomputable def baseChange (A : Type*) [Ring A] [Algebra R A] :
    DescentDatum R S (S ⊗[R] A) where
  coaction := Algebra.TensorProduct.map (AlgHom.id S S) Algebra.TensorProduct.includeRight
  counit_coaction x := by
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  coassoc x := by
    induction x using TensorProduct.inductionOn with
    | tmul s a => simp
    | add x y hx hy => simp only [map_add, hx, hy]

@[simp]
theorem baseChange_coaction_tmul {A : Type*} [Ring A] [Algebra R A] (s : S) (a : A) :
    (baseChange R S A).coaction (s ⊗ₜ a) = s ⊗ₜ (1 ⊗ₜ a) :=
  (rfl)

/-- If `S` is faithfully flat over `R`, the canonical descent datum on `S ⊗[R] A` descends to
the image of `A`, i.e. the elements of the form `1 ⊗ a`. -/
theorem descended_baseChange [Module.FaithfullyFlat R S] (A : Type*) [Ring A] [Algebra R A] :
    (baseChange R S A).descended = (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).range
    := by
  ext x
  have hθ : (baseChange R S A).coaction x = (TensorProduct.mk R S A 1).lTensor S x := by
    induction x using TensorProduct.inductionOn with
    | tmul s a => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [mem_descended_iff, hθ, ← sub_eq_zero, AlgHom.mem_range]
  exact (Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one S A x).trans
    (by simp [eq_comm])

/-- **Uniqueness of descent.** If `S` is faithfully flat over `R`, `A` is an `R`-algebra and
`e : S ⊗[R] A ≃ B` is an `S`-algebra isomorphism carrying `1 ⊗ A` into the descended algebra
(equivalently, carrying the canonical descent datum on `S ⊗[R] A` to `D`), then
`a ↦ e (1 ⊗ a)` is an isomorphism of `A` onto `D.descended`. -/
noncomputable def equivDescended [Module.FaithfullyFlat R S] {A : Type*} [Ring A] [Algebra R A]
    (e : S ⊗[R] A ≃ₐ[S] B) (he : ∀ a : A, e (1 ⊗ₜ a) ∈ D.descended) : A ≃ₐ[R] D.descended :=
  AlgEquiv.ofBijective
    (((e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight).codRestrict _
      fun a ↦ by simpa using he a)
    (by
      refine ⟨fun a a' h ↦ ?_, fun ⟨b, hb⟩ ↦ ?_⟩
      · have h' : (1 : S) ⊗ₜ[R] (a - a') = 0 := by
          rw [tmul_sub, sub_eq_zero]
          exact e.injective congr($h.1)
        simpa [sub_eq_zero] using h'
      -- The coaction of `D` is the transport of the canonical coaction along `e`.
      have hcompat : ∀ x, D.coaction (e x) =
          Algebra.TensorProduct.map (AlgHom.id R S) (e.toAlgHom.restrictScalars R)
            ((baseChange R S A).coaction x) := by
        intro x
        induction x using TensorProduct.inductionOn with
        | tmul s a =>
          have h1 : e (s ⊗ₜ a) = s • e (1 ⊗ₜ a) := by
            rw [← map_smul, smul_tmul', smul_eq_mul, mul_one]
          simp [h1, (mem_descended_iff _).mp (he a), smul_tmul']
        | add x y hx hy => simp only [map_add, hx, hy]
      have hmem : e.symm b ∈ (baseChange R S A).descended := by
        refine (mem_descended_iff _).mpr ?_
        have hinj := (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[R] S)
          (e.restrictScalars R)).injective
        apply hinj
        have := hcompat (e.symm b)
        simp only [AlgEquiv.apply_symm_apply] at this
        simpa [← this] using hb
      rw [descended_baseChange] at hmem
      obtain ⟨a, ha⟩ := hmem
      have ha' : (1 : S) ⊗ₜ[R] a = e.symm b := by simpa using ha
      exact ⟨a, Subtype.ext <| by simp [ha']⟩)

@[simp]
theorem coe_equivDescended_apply [Module.FaithfullyFlat R S] {A : Type*} [Ring A] [Algebra R A]
    (e : S ⊗[R] A ≃ₐ[S] B) (he : ∀ a : A, e (1 ⊗ₜ a) ∈ D.descended) (a : A) :
    (D.equivDescended e he a : B) = e (1 ⊗ₜ a) :=
  (rfl)

@[simp]
theorem baseChangeEquiv_symm_coe [Module.Flat R S] (a : D.descended) :
    D.baseChangeEquiv.symm a = 1 ⊗ₜ a := by
  rw [AlgEquiv.symm_apply_eq, baseChangeEquiv_tmul, one_smul]

/-! ### Morphisms of descent data -/

section Hom

variable {B' B'' : Type*} [Ring B'] [Algebra R B'] [Algebra S B'] [IsScalarTower R S B']
  [Ring B''] [Algebra R B''] [Algebra S B''] [IsScalarTower R S B'']

/-- A morphism of descent data from `D` on `B` to `D'` on `B'`: an `S`-algebra map `f : B → B'`
intertwining the coactions, `θ' ∘ f = (id ⊗ f) ∘ θ`. -/
@[ext]
structure Hom (D : DescentDatum R S B) (D' : DescentDatum R S B') where
  /-- The underlying `S`-algebra map. -/
  toAlgHom : B →ₐ[S] B'
  /-- The map intertwines the coactions. -/
  coaction_toAlgHom (b : B) : D'.coaction (toAlgHom b) =
    Algebra.TensorProduct.map (AlgHom.id R S) (toAlgHom.restrictScalars R) (D.coaction b)

namespace Hom

variable {D : DescentDatum R S B} {D' : DescentDatum R S B'} {D'' : DescentDatum R S B''}

variable (D) in
/-- The identity morphism of a descent datum. -/
def id : Hom D D where
  toAlgHom := AlgHom.id S B
  -- `(AlgHom.id S B).restrictScalars R` is definitionally `AlgHom.id R B`; Mathlib has no
  -- `AlgHom.restrictScalars_id` simp lemma, so `simp` cannot see this and we unify directly.
  coaction_toAlgHom b := (DFunLike.congr_fun Algebra.TensorProduct.map_id (D.coaction b)).symm

variable (D) in
@[simp]
theorem id_toAlgHom : (Hom.id D).toAlgHom = AlgHom.id S B :=
  (rfl)

/-- The composition of morphisms of descent data. -/
def comp (g : Hom D' D'') (f : Hom D D') : Hom D D'' where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  coaction_toAlgHom b := by
    have hc : (g.toAlgHom.comp f.toAlgHom).restrictScalars R =
        (g.toAlgHom.restrictScalars R).comp (f.toAlgHom.restrictScalars R) :=
      AlgHom.ext fun _ ↦ rfl
    rw [AlgHom.comp_apply, g.coaction_toAlgHom, f.coaction_toAlgHom, ← AlgHom.comp_apply,
      ← Algebra.TensorProduct.map_comp, hc, AlgHom.comp_id]

@[simp]
theorem comp_toAlgHom (g : Hom D' D'') (f : Hom D D') :
    (g.comp f).toAlgHom = g.toAlgHom.comp f.toAlgHom :=
  (rfl)

/-- A morphism of descent data maps the descended algebra into the descended algebra. -/
theorem mem_descended (f : Hom D D') {b : B} (hb : b ∈ D.descended) :
    f.toAlgHom b ∈ D'.descended := by
  rw [mem_descended_iff] at hb ⊢
  rw [f.coaction_toAlgHom, hb]
  simp

/-- The morphism of descended algebras induced by a morphism of descent data. -/
def descend (f : Hom D D') : D.descended →ₐ[R] D'.descended :=
  ((f.toAlgHom.restrictScalars R).comp D.descended.val).codRestrict _
    fun a ↦ f.mem_descended a.2

@[simp]
theorem coe_descend_apply (f : Hom D D') (a : D.descended) :
    (f.descend a : B') = f.toAlgHom a :=
  (rfl)

@[simp]
theorem descend_id : (Hom.id D).descend = AlgHom.id R D.descended :=
  (rfl)

@[simp]
theorem descend_comp (g : Hom D' D'') (f : Hom D D') :
    (g.comp f).descend = g.descend.comp f.descend :=
  (rfl)

/-- Under the effectivity isomorphisms `baseChangeEquiv`, a morphism of descent data is the base
change of the induced morphism of descended algebras. -/
theorem toAlgHom_baseChangeEquiv [Module.Flat R S] (f : Hom D D') (x : S ⊗[R] D.descended) :
    f.toAlgHom (D.baseChangeEquiv x) =
      D'.baseChangeEquiv (Algebra.TensorProduct.map (AlgHom.id S S) f.descend x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem descend_injective [Module.Flat R S] :
    Function.Injective (descend : Hom D D' → D.descended →ₐ[R] D'.descended) := by
  intro f g h
  ext b
  obtain ⟨x, rfl⟩ := D.baseChangeEquiv.surjective b
  rw [toAlgHom_baseChangeEquiv, toAlgHom_baseChangeEquiv, h]

/-- The base change of a morphism of descended algebras, transported along `baseChangeEquiv`. -/
private noncomputable def ofDescend [Module.Flat R S] (φ : D.descended →ₐ[R] D'.descended) :
    Hom D D' where
  toAlgHom := (D'.baseChangeEquiv.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id S S) φ)).comp
    D.baseChangeEquiv.symm.toAlgHom
  coaction_toAlgHom b := by
    obtain ⟨x, rfl⟩ := D.baseChangeEquiv.surjective b
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      have ha : D.coaction a = 1 ⊗ₜ (a : B) := a.2
      have hφa : D'.coaction (φ a) = 1 ⊗ₜ ((φ a : D'.descended) : B') := (φ a).2
      simp [ha, hφa, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

private theorem descend_ofDescend [Module.Flat R S] (φ : D.descended →ₐ[R] D'.descended) :
    (ofDescend φ).descend = φ := by
  ext a
  simp [ofDescend]

end Hom

/-- **Descent of morphisms.** If `S` is flat over `R`, morphisms of descent data correspond to
morphisms of the descended algebras. -/
noncomputable def homEquiv [Module.Flat R S] (D : DescentDatum R S B) (D' : DescentDatum R S B') :
    Hom D D' ≃ (D.descended →ₐ[R] D'.descended) where
  toFun := Hom.descend
  invFun := Hom.ofDescend
  left_inv f := Hom.descend_injective (Hom.descend_ofDescend f.descend)
  right_inv := Hom.descend_ofDescend

@[simp]
theorem homEquiv_apply [Module.Flat R S] (D : DescentDatum R S B) (D' : DescentDatum R S B')
    (f : Hom D D') : homEquiv D D' f = f.descend :=
  (rfl)

end Hom

section BaseChange

variable {A A' : Type*} [Ring A] [Algebra R A] [Ring A'] [Algebra R A']

/-- The morphism of canonical descent data `S ⊗[R] A → S ⊗[R] A'` induced by an `R`-algebra map
`A → A'`. -/
noncomputable def Hom.baseChange (f : A →ₐ[R] A') :
    Hom (DescentDatum.baseChange R S A) (DescentDatum.baseChange R S A') where
  toAlgHom := Algebra.TensorProduct.map (AlgHom.id S S) f
  coaction_toAlgHom x := by
    induction x using TensorProduct.inductionOn with
    | tmul s a => simp
    | add x y hx hy => simp only [map_add, hx, hy]

@[simp]
theorem Hom.baseChange_toAlgHom (f : A →ₐ[R] A') :
    (Hom.baseChange (S := S) f).toAlgHom = Algebra.TensorProduct.map (AlgHom.id S S) f :=
  (rfl)

/-- The isomorphism of `A` with the algebra descended from the canonical descent datum on
`S ⊗[R] A`, for `S` faithfully flat over `R`. -/
private noncomputable def equivDescendedBaseChange [Module.FaithfullyFlat R S] :
    A ≃ₐ[R] (DescentDatum.baseChange R S A).descended :=
  (DescentDatum.baseChange R S A).equivDescended AlgEquiv.refl fun a ↦ by simp

private theorem coe_equivDescendedBaseChange_apply [Module.FaithfullyFlat R S] (a : A) :
    (equivDescendedBaseChange (R := R) (S := S) a : S ⊗[R] A) = 1 ⊗ₜ a :=
  (rfl)

/-- **Descent of morphisms of affine schemes.** If `S` is faithfully flat over `R`, the
`R`-algebra maps `A → A'` are exactly the morphisms between the canonical descent data on
`S ⊗[R] A` and `S ⊗[R] A'`, via `f ↦ id ⊗ f`. -/
noncomputable def baseChangeHomEquiv [Module.FaithfullyFlat R S] :
    (A →ₐ[R] A') ≃ Hom (DescentDatum.baseChange R S A) (DescentDatum.baseChange R S A') :=
  Equiv.ofBijective Hom.baseChange <| by
    refine ⟨fun f g h ↦ AlgHom.ext fun a ↦ ?_, fun h ↦ ?_⟩
    · refine Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) A' ?_
      simpa using congr($(congrArg Hom.toAlgHom h) (1 ⊗ₜ a))
    refine ⟨(equivDescendedBaseChange.symm.toAlgHom.comp h.descend).comp
      equivDescendedBaseChange.toAlgHom, Hom.ext ?_⟩
    refine Algebra.TensorProduct.ext' fun s a ↦ ?_
    have h1 : h.toAlgHom (s ⊗ₜ a) = s • h.toAlgHom (1 ⊗ₜ a) := by
      rw [← map_smul, smul_tmul', smul_eq_mul, mul_one]
    have h2 : (1 : S) ⊗ₜ[R] equivDescendedBaseChange.symm (h.descend (equivDescendedBaseChange a)) =
        h.toAlgHom (1 ⊗ₜ a) := by
      rw [← coe_equivDescendedBaseChange_apply, AlgEquiv.apply_symm_apply, Hom.coe_descend_apply,
        coe_equivDescendedBaseChange_apply]
    simp [h1, ← h2, smul_tmul']

@[simp]
theorem baseChangeHomEquiv_apply [Module.FaithfullyFlat R S] (f : A →ₐ[R] A') :
    baseChangeHomEquiv (S := S) f = Hom.baseChange f :=
  (rfl)

/-- The `R`-algebra map descended from a morphism `h` of canonical descent data is characterised
by `1 ⊗ (baseChangeHomEquiv.symm h a) = h (1 ⊗ a)`. -/
theorem tmul_baseChangeHomEquiv_symm_apply [Module.FaithfullyFlat R S]
    (h : Hom (DescentDatum.baseChange R S A) (DescentDatum.baseChange R S A')) (a : A) :
    (1 : S) ⊗ₜ[R] baseChangeHomEquiv.symm h a = h.toAlgHom (1 ⊗ₜ a) := by
  obtain ⟨f, rfl⟩ := baseChangeHomEquiv.surjective h
  rw [Equiv.symm_apply_apply]
  simp

end BaseChange

/-! ### Change of the base ring

If `S` is faithfully flat over `R`, the equalizer `D.descended → B ⇉ S ⊗[R] B` stays an equalizer
after tensoring with any `R`-module. Hence forming the descended algebra commutes with arbitrary
base change `R → R'`. -/

section ChangeOfBase

variable [Module.FaithfullyFlat R S]

/-- The isomorphism `S ⊗[R] (M ⊗[R] D.descended) ≃ M ⊗[R] B`, `s ⊗ m ⊗ a ↦ m ⊗ s • a`. -/
private noncomputable def leftCommBaseChangeEquiv (M : Type*) [AddCommGroup M] [Module R M] :
    S ⊗[R] (M ⊗[R] D.descended) ≃ₗ[R] M ⊗[R] B :=
  TensorProduct.leftComm R S M D.descended ≪≫ₗ
    (D.baseChangeEquiv.toLinearEquiv.restrictScalars R).lTensor M

/-- The isomorphism `S ⊗[R] (S ⊗[R] (M ⊗[R] D.descended)) ≃ M ⊗[R] (S ⊗[R] B)`,
`s ⊗ t ⊗ m ⊗ a ↦ m ⊗ s ⊗ t • a`. -/
private noncomputable def leftCommBaseChangeEquiv₂ (M : Type*) [AddCommGroup M] [Module R M] :
    S ⊗[R] (S ⊗[R] (M ⊗[R] D.descended)) ≃ₗ[R] M ⊗[R] (S ⊗[R] B) :=
  (TensorProduct.leftComm R S M D.descended).lTensor S ≪≫ₗ TensorProduct.leftComm R S M _ ≪≫ₗ
    ((D.baseChangeEquiv.toLinearEquiv.restrictScalars R).lTensor S).lTensor M

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Under `leftCommBaseChangeEquiv`, the inclusion `M ⊗ D.descended → M ⊗ B` is the first map
`x ↦ 1 ⊗ x` of the Amitsur complex of `M ⊗ D.descended`. -/
private theorem lTensor_descended_val_eq :
    D.descended.val.toLinearMap.lTensor M =
      (D.leftCommBaseChangeEquiv M).toLinearMap ∘ₗ
        TensorProduct.mk R S (M ⊗[R] D.descended) 1 := by
  ext m a
  simp [leftCommBaseChangeEquiv]

/-- If `S` is faithfully flat over `R`, the inclusion `D.descended → B` is universally
injective: it stays injective after tensoring with any `R`-module `M`. -/
theorem lTensor_descended_val_injective :
    Function.Injective (D.descended.val.toLinearMap.lTensor M) := by
  rw [lTensor_descended_val_eq, LinearMap.coe_comp, LinearEquiv.coe_coe,
    EquivLike.comp_injective]
  exact Module.FaithfullyFlat.tensorProduct_mk_injective _

/-- **The descended algebra is a universal equalizer.** If `S` is faithfully flat over `R`, then
for every `R`-module `M` the sequence `M ⊗ D.descended → M ⊗ B → M ⊗ (S ⊗ B)`, whose second map
is `m ⊗ b ↦ m ⊗ (θ b - 1 ⊗ b)`, is exact. -/
theorem exact_lTensor_descended_val :
    Function.Exact (D.descended.val.toLinearMap.lTensor M)
      (((D.coaction.restrictScalars R).toLinearMap -
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toLinearMap).lTensor M) := by
  -- Transport the Amitsur complex of `M ⊗ D.descended` along the effectivity isomorphism.
  refine Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := LinearEquiv.refl R _)
    (e₂ := D.leftCommBaseChangeEquiv M) (e₃ := D.leftCommBaseChangeEquiv₂ M)
    (by rw [LinearEquiv.refl_toLinearMap, LinearMap.comp_id, lTensor_descended_val_eq]) ?_
    (Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one S _)
  ext s m a
  have ha : D.coaction a = 1 ⊗ₜ (a : B) := a.2
  simp [leftCommBaseChangeEquiv, leftCommBaseChangeEquiv₂, ha, Algebra.smul_def,
    Algebra.TensorProduct.algebraMap_apply]

end ChangeOfBase

/-! ### Comparison along a base change of descent data -/

section Comparison

variable {R' S' B' : Type*} [CommRing R'] [CommRing S'] [Ring B'] [Algebra R R'] [Algebra R' S']
  [Algebra R S'] [IsScalarTower R R' S'] [Algebra R' B'] [Algebra R B'] [IsScalarTower R R' B']
  [Algebra S' B'] [IsScalarTower R' S' B'] {D' : DescentDatum R' S' B'}
  {φ : S →ₐ[R] S'} {ψ : B →ₐ[R] B'}
  (hθ : ∀ b, D'.coaction (ψ b) = (TensorProduct.mapOfCompatibleSMul R' R R S' B' ∘ₗ
    TensorProduct.map φ.toLinearMap ψ.toLinearMap) (D.coaction b))

include hθ in
private theorem mem_descended_of_coaction_comp (a : D.descended) : ψ a ∈ D'.descended := by
  have ha : D.coaction a = 1 ⊗ₜ (a : B) := a.2
  simp [hθ, ha]

/-- The comparison map `R' ⊗[R] D.descended → D'.descended`, `r ⊗ a ↦ r • ψ a`. -/
private noncomputable def tensorDescendedHom : R' ⊗[R] D.descended →ₐ[R'] D'.descended :=
  (Algebra.TensorProduct.lift (Algebra.ofId R' B') (ψ.comp D.descended.val) fun r a ↦ by
    rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left r _).codRestrict
    D'.descended fun x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul r a =>
      rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, ← Algebra.smul_def]
      exact Subalgebra.smul_mem _ (D.mem_descended_of_coaction_comp hθ a) r
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

private theorem coe_tensorDescendedHom (hψ : IsBaseChange R' (ψ.toLinearMap : B →ₗ[R] B'))
    (x : R' ⊗[R] D.descended) :
    (D.tensorDescendedHom hθ x : B') = hψ.equiv (D.descended.val.toLinearMap.lTensor R' x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp [tensorDescendedHom, IsBaseChange.equiv_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]

include hθ in
/-- Under the identification `R' ⊗[R] (S ⊗[R] B) ≃ S' ⊗[R'] B'`, the base change of the
equalizer pair of `D` becomes the equalizer pair of `D'`. -/
private theorem equiv_lTensor_coaction_sub (hφ : IsBaseChange R' φ.toLinearMap)
    (hψ : IsBaseChange R' (ψ.toLinearMap : B →ₗ[R] B')) (y : R' ⊗[R] B) :
    (hφ.tensorProduct hψ).equiv (((D.coaction.restrictScalars R).toLinearMap -
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toLinearMap).lTensor R' y) =
      D'.coaction (hψ.equiv y) - 1 ⊗ₜ hψ.equiv y := by
  induction y using TensorProduct.inductionOn with
  | tmul r b =>
    rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul,
      LinearMap.sub_apply, map_sub, smul_sub]
    simp only [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars']
    rw [← hθ, ← algebraMap_smul S' r (ψ b), map_smul, algebraMap_smul]
    simp [tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, tmul_add]; abel

include hθ in
private theorem tensorDescendedHom_bijective [Module.FaithfullyFlat R S]
    (hφ : IsBaseChange R' φ.toLinearMap) (hψ : IsBaseChange R' (ψ.toLinearMap : B →ₗ[R] B')) :
    Function.Bijective (D.tensorDescendedHom hθ) := by
  refine ⟨fun x y h ↦ D.lTensor_descended_val_injective R' (hψ.equiv.injective ?_),
    fun x' ↦ ?_⟩
  · rw [← D.coe_tensorDescendedHom hθ hψ, ← D.coe_tensorDescendedHom hθ hψ, h]
  obtain ⟨y, hy'⟩ := hψ.equiv.surjective x'
  -- `y` satisfies the base-changed descent condition, so it comes from `R' ⊗ D.descended`.
  obtain ⟨z, rfl⟩ := (D.exact_lTensor_descended_val R' y).mp <|
    (hφ.tensorProduct hψ).equiv.injective <| by
      rw [D.equiv_lTensor_coaction_sub hθ hφ hψ, hy', map_zero, sub_eq_zero]
      exact x'.2
  exact ⟨z, Subtype.ext ((D.coe_tensorDescendedHom hθ hψ z).trans hy')⟩

/-- **Descent commutes with base change.** Let `S` be faithfully flat over `R`, let `R → R'` be
any ring map, and let `D'` be a descent datum on `B'` relative to `R' → S'`. Suppose that
`φ : S → S'` and `ψ : B → B'` exhibit `S'` and `B'` as the base changes `R' ⊗[R] S` and
`R' ⊗[R] B`, and that `ψ` intertwines the coactions, `θ' ∘ ψ = (φ ⊗ ψ) ∘ θ`. Then
`r ⊗ a ↦ r • ψ a` is an isomorphism `R' ⊗[R] D.descended ≃ D'.descended`. -/
noncomputable def tensorDescendedEquiv [Module.FaithfullyFlat R S]
    (hφ : IsBaseChange R' φ.toLinearMap) (hψ : IsBaseChange R' (ψ.toLinearMap : B →ₗ[R] B')) :
    R' ⊗[R] D.descended ≃ₐ[R'] D'.descended :=
  AlgEquiv.ofBijective (D.tensorDescendedHom hθ) (D.tensorDescendedHom_bijective hθ hφ hψ)

@[simp]
theorem coe_tensorDescendedEquiv_tmul [Module.FaithfullyFlat R S]
    (hφ : IsBaseChange R' φ.toLinearMap) (hψ : IsBaseChange R' (ψ.toLinearMap : B →ₗ[R] B'))
    (r : R') (a : D.descended) :
    (D.tensorDescendedEquiv hθ hφ hψ (r ⊗ₜ a) : B') = r • ψ a := by
  simp [tensorDescendedEquiv, tensorDescendedHom, Algebra.smul_def]

end Comparison

end DescentDatum

end Algebra

end TauCeti
