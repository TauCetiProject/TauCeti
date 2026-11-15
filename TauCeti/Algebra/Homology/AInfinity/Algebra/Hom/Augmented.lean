/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation
import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar
public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Unital
public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation

/-!
# Augmented `A∞` morphisms and equivalence with reduced `A∞` algebras

Between augmented uncurved `A∞` algebras `(A, ε_A)` and `(B, ε_B)`, an `A∞` morphism `f : A ⟶ B`
is **augmented** (`TauCeti.AInfinityHom.IsAugmented`) when it is strictly unital and
`ε_B ∘ f.taylor` reads only `ε_A` on single letters (`ε_B ∘ f₁ = ε_A` and `ε_B ∘ fₙ = 0` for
`n ≥ 2`).

Splitting each augmented `A∞` algebra as `R · 1 ⊕ ker ε` induces a functorial equivalence
`TauCeti.AInfinityAlgebra.Augmentation.augmentedHomEquiv` between strictly unital augmented `A∞`
morphisms `(A, ε_A) ⟶ (B, ε_B)` and arbitrary `A∞` morphisms `ker ε_A ⟶ ker ε_B` between their
reduced augmentation ideals. For a DG algebra `B`, `DGAlgAugmentation.toAInfinityAugmentation`
embeds DG augmentations into `A∞` augmentations compatibly with `isAugmented_toAInfinityHom_iff`.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 2.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

universe uR uA uB uC

section Predicate

variable {R : Type uR} [CommRing R]

namespace AInfinityHom

section Defs

variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- An `A∞` morphism between augmented `A∞` algebras is **augmented** when it is strictly unital
and `ε_B ∘ f.taylor` reads only the source augmentation on single letters. -/
structure IsAugmented (f : AInfinityHom AA BB)
    (εA : AA.Augmentation) (εB : BB.Augmentation) : Prop where
  /-- The morphism is strictly unital for the strict units of `εA` and `εB`. -/
  isStrictlyUnital : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit
  /-- Composing `f.taylor` with `εB` extracts `εA` of the length-one component. -/
  comp_taylor : εB.toLinearMap ∘ₗ f.taylor = εA.toLinearMap ∘ₗ ReducedTensorWords.letter R A

namespace IsAugmented

variable {f : AInfinityHom AA BB} {εA : AA.Augmentation} {εB : BB.Augmentation}

/-- The linear part of an augmented `A∞` morphism intertwines the augmentations. -/
theorem comp_linearPart (hf : f.IsAugmented εA εB) :
    εB.toLinearMap ∘ₗ f.linearPart = εA.toLinearMap :=
  LinearMap.ext fun a ↦ by
    simpa using LinearMap.congr_fun hf.comp_taylor (ReducedTensorWords.ofLetter R A a)

/-- Evaluated on an element, the linear part preserves the augmentation. -/
theorem map_linearPart (hf : f.IsAugmented εA εB) (a : A) : εB (f.linearPart a) = εA a :=
  LinearMap.congr_fun hf.comp_linearPart a

/-- Every higher component of an augmented `A∞` morphism lands in the target augmentation ideal. -/
theorem map_component_eq_zero (hf : f.IsAugmented εA εB) {n : ℕ} (hn : n ≠ 1) (x : Fin n → A) :
    εB (f.component n x) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hnpos := Nat.pos_of_ne_zero hn0
    have hne1 : (⟨n, hnpos⟩ : {k : ℕ // 0 < k}) ≠ 1 := fun h ↦
      hn (by simpa using congrArg Subtype.val h)
    rw [component_apply f n hnpos]
    simpa [ReducedTensorWords.letter_of_of_ne_one R A hne1] using
      LinearMap.congr_fun hf.comp_taylor (ReducedTensorWords.of R A ⟨n, hnpos⟩
        (PiTensorProduct.tprod R fun i ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)))

/-- Augmented `A∞` morphisms compose. -/
theorem comp {C : Type uC} [AddCommGroup C] [Module R C] {CC : AInfinityAlgebra R C}
    {g : AInfinityHom BB CC} {εC : CC.Augmentation}
    (hg : g.IsAugmented εB εC) (hf : f.IsAugmented εA εB) :
    (g.comp f).IsAugmented εA εC where
  isStrictlyUnital := hg.isStrictlyUnital.comp hf.isStrictlyUnital
  comp_taylor := by
    rw [taylor_comp, ← LinearMap.comp_assoc, hg.comp_taylor, LinearMap.comp_assoc,
      ← f.taylor_def, hf.comp_taylor]

end IsAugmented

/-- Componentwise characterization of `IsAugmented` in terms of `linearPart` and `component`. -/
theorem isAugmented_iff_component {f : AInfinityHom AA BB}
    {εA : AA.Augmentation} {εB : BB.Augmentation} :
    f.IsAugmented εA εB ↔
      f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit ∧
        εB.toLinearMap ∘ₗ f.linearPart = εA.toLinearMap ∧
        ∀ {n : ℕ}, n ≠ 1 → ∀ x : Fin n → A, εB (f.component n x) = 0 := by
  refine ⟨fun hf ↦ ⟨hf.isStrictlyUnital, hf.comp_linearPart, fun hn x ↦
    hf.map_component_eq_zero hn x⟩, fun ⟨hunital, hlin, hcomp⟩ ↦
      ⟨hunital, ReducedTensorWords.linearMap_ext R A fun ⟨k, hk⟩ x ↦ ?_⟩⟩
  rcases eq_or_ne k 1 with rfl | hn1
  · rw [ReducedTensorWords.of_tprod_eq_subword R hk x,
      ReducedTensorWords.subword_one R A x Nat.one_pos]
    simpa using LinearMap.congr_fun hlin (x ⟨0, Nat.one_pos⟩)
  · have hne1 : (⟨k, hk⟩ : {n : ℕ // 0 < n}) ≠ 1 := fun h ↦
      hn1 (by simpa using congrArg Subtype.val h)
    have htw : f.taylor (ReducedTensorWords.of R A ⟨k, hk⟩ (PiTensorProduct.tprod R x)) =
        f.component k (fun i ↦ AA.grading.koszulTwist ((k : ℤ) - 1 - i) (x i)) := by
      rw [component_apply f k hk]; simp only [InternalGrading.koszulTwist_koszulTwist]
    simp only [LinearMap.comp_apply, ReducedTensorWords.letter_of_of_ne_one R A hne1, map_zero, htw]
    exact hcomp hn1 _

/-- A strict `A∞` morphism is augmented iff its linear part preserves the unit and augmentation. -/
theorem IsStrict.isAugmented_iff {f : AInfinityHom AA BB}
    {εA : AA.Augmentation} {εB : BB.Augmentation} (hf : f.IsStrict) :
    f.IsAugmented εA εB ↔
      f.linearPart εA.unit = εB.unit ∧ εB.toLinearMap ∘ₗ f.linearPart = εA.toLinearMap := by
  refine ⟨fun h ↦ ⟨h.isStrictlyUnital.map_unit, h.comp_linearPart⟩, fun ⟨hu, hε⟩ ↦
    ⟨hf.isStrictlyUnital hu, ?_⟩⟩
  rw [(isStrict_iff f).mp hf, ← LinearMap.comp_assoc, hε]

end Defs

/-- The identity `A∞` morphism is augmented for every augmentation. -/
@[simp]
theorem isAugmented_id {A : Type uA} [AddCommGroup A] [Module R A] {AA : AInfinityAlgebra R A}
    (εA : AA.Augmentation) : (AInfinityHom.id AA).IsAugmented εA εA where
  isStrictlyUnital := isStrictlyUnital_id εA.isStrictUnit
  comp_taylor := by rw [taylor_id]

end AInfinityHom

end Predicate

section Splitting

variable {R : Type uR} [CommRing R]

private theorem letter_map_apply {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (w : ReducedTensorWords R M) :
    ReducedTensorWords.letter R N (ReducedTensorWords.map (R := R) g w) =
      g (ReducedTensorWords.letter R M w) :=
  LinearMap.congr_fun (ReducedTensorWords.letter_comp_map g) w

namespace AInfinityAlgebra.Augmentation

section Single

variable {A : Type uA} [AddCommGroup A] [Module R A] {AA : AInfinityAlgebra R A}

/-- The inclusion of the reduced augmentation ideal into `A` as a strict `A∞` morphism. -/
noncomputable def inclusionStrictHom (ε : AA.Augmentation) :
    AInfinityStrictHom ε.reducedAlgebra AA where
  toLinearMap := ε.augmentationIdeal.subtype
  map_mem' hx := by simpa using hx
  map_m' _ := by ext; simp

/-- The underlying linear map of `inclusionStrictHom` is the submodule inclusion. -/
@[simp]
theorem inclusionStrictHom_toLinearMap (ε : AA.Augmentation) :
    ε.inclusionStrictHom.toLinearMap = ε.augmentationIdeal.subtype := (rfl)

/-- The reduced-part projection vanishes on the strict unit. -/
@[simp]
theorem reducedPart_unit (ε : AA.Augmentation) : ε.reducedPart ε.unit = 0 := Subtype.ext (by simp)

/-- Elements of an augmented `A∞` algebra agree iff their augmentations and reduced parts agree. -/
theorem eq_iff_map_eq_and_reducedPart_eq (ε : AA.Augmentation) {x y : A} :
    x = y ↔ ε x = ε y ∧ ε.reducedPart x = ε.reducedPart y := by
  refine ⟨fun h ↦ by subst h; exact ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ ↦ ε.splitLinearEquiv.injective ?_⟩
  rw [splitLinearEquiv_apply, splitLinearEquiv_apply, h1, h2]

/-- The reduced-part projection is homogeneous of degree zero. -/
theorem isHomogeneous_reducedPart (ε : AA.Augmentation) :
    LinearMap.IsHomogeneous ε.reducedPart AA.grading.piece ε.reducedAlgebra.grading.piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun p x hx ↦ ?_
  rw [add_zero, reducedAlgebra_grading, reducedGrading_piece, Submodule.mem_comap,
    Submodule.subtype_apply, coe_reducedPart]
  rcases eq_or_ne p 0 with rfl | hp
  · exact sub_mem hx (Submodule.smul_mem _ _ ε.isStrictUnit.degree_zero)
  · rw [ε.map_of_mem_ne_zero p x hx hp, zero_smul, sub_zero]; exact hx

/-- Any `A∞` morphism into `A` whose Taylor map lands in `ker ε` factors uniquely through
`ε.reducedAlgebra`. -/
noncomputable def homToReducedEquiv {M : Type*} [AddCommGroup M] [Module R M]
    (II : AInfinityAlgebra R M) (ε : AA.Augmentation) :
    {f : AInfinityHom II AA // ∀ z, f.taylor z ∈ ε.augmentationIdeal} ≃
      AInfinityHom II ε.reducedAlgebra where
  toFun f :=
    let t := ε.reducedPart ∘ₗ f.1.taylor
    have ht : LinearMap.IsHomogeneous t (ReducedTensorWords.gradedPiece (II.grading.shift 1))
        (ε.reducedAlgebra.grading.shift 1).piece 0 := by
      simpa only [add_zero] using
        (LinearMap.isHomogeneous_shift_piece_iff.mpr ε.isHomogeneous_reducedPart).comp
          f.1.isHomogeneous_taylor
    AInfinityHom.ofTaylor t ht <| by
      have hsub : ε.augmentationIdeal.subtype ∘ₗ t = f.1.taylor :=
        LinearMap.ext fun z ↦ by simp [t, ε.coe_reducedPart, (ε.mem_augmentationIdeal).mp (f.2 z)]
      have hcoalg : ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype ∘ₗ
          ReducedTensorWords.coalgHom R t = f.1.barMap := by
        rw [ReducedTensorWords.map_comp_coalgHom, hsub, ← f.1.barMap_eq_coalgHom]
      have hinc := ε.inclusionStrictHom.taylor_comp_barMap
      rw [AInfinityStrictHom.barMap_def, inclusionStrictHom_toLinearMap] at hinc
      refine LinearMap.ext fun z ↦ Subtype.ext ?_
      have h1 := LinearMap.congr_fun (congrArg (· ∘ₗ ReducedTensorWords.coalgHom R t) hinc.symm) z
      have h2 := LinearMap.congr_fun (congrArg (· ∘ₗ II.barDifferential) hsub) z
      simp only [t, LinearMap.comp_apply, Submodule.subtype_apply] at h1 h2 ⊢
      rw [h1, ← LinearMap.comp_apply (ReducedTensorWords.map _ _), hcoalg,
        ← LinearMap.comp_apply AA.taylor, f.1.taylor_comp_barMap, LinearMap.comp_apply]
      exact h2.symm
  invFun g := ⟨ε.inclusionStrictHom.toAInfinityHom.comp g, fun z ↦ by
    rw [AInfinityStrictHom.taylor_toAInfinityHom_comp]; exact (g.taylor z).2⟩
  left_inv f := Subtype.ext <| AInfinityHom.ext <| by
    rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, AInfinityHom.taylor_ofTaylor]
    exact LinearMap.ext fun z ↦ by simp [ε.coe_reducedPart, (ε.mem_augmentationIdeal).mp (f.2 z)]
  right_inv g := AInfinityHom.ext <| by
    rw [AInfinityHom.taylor_ofTaylor, AInfinityStrictHom.taylor_toAInfinityHom_comp]
    exact LinearMap.ext fun _ ↦ by simp

/-- The Taylor map of `homToReducedEquiv II f` projects `f.taylor` onto `ker ε`. -/
@[simp]
theorem taylor_homToReducedEquiv {M : Type*} [AddCommGroup M] [Module R M]
    (II : AInfinityAlgebra R M) (ε : AA.Augmentation)
    (f : {f : AInfinityHom II AA // ∀ z, f.taylor z ∈ ε.augmentationIdeal}) :
    (ε.homToReducedEquiv II f).taylor = ε.reducedPart ∘ₗ f.1.taylor := by simp [homToReducedEquiv]

/-- The inverse of `homToReducedEquiv` postcomposes with `inclusionStrictHom`. -/
@[simp]
theorem homToReducedEquiv_symm_apply {M : Type*} [AddCommGroup M] [Module R M]
    (II : AInfinityAlgebra R M) (ε : AA.Augmentation) (g : AInfinityHom II ε.reducedAlgebra) :
    ((ε.homToReducedEquiv II).symm g).1 = ε.inclusionStrictHom.toAInfinityHom.comp g := (rfl)

/-- Source naturality of `homToReducedEquiv` under precomposition with an `A∞` morphism. -/
theorem homToReducedEquiv_comp {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (II : AInfinityAlgebra R M) (JJ : AInfinityAlgebra R N)
    (ε : AA.Augmentation) (f : {f : AInfinityHom JJ AA // ∀ z, f.taylor z ∈ ε.augmentationIdeal})
    (h : AInfinityHom II JJ) :
    ε.homToReducedEquiv II ⟨f.1.comp h, fun _ ↦ by rw [AInfinityHom.taylor_comp]; exact f.2 _⟩ =
      (ε.homToReducedEquiv JJ f).comp h :=
  AInfinityHom.ext <| by simp [AInfinityHom.taylor_comp, LinearMap.comp_assoc]

/-- An augmentation is invariant under any Koszul twist, since it vanishes outside degree zero. -/
theorem comp_koszulTwist (ε : AA.Augmentation) (q : ℤ) :
    ε.toLinearMap ∘ₗ AA.grading.koszulTwist q = ε.toLinearMap := by
  refine AA.grading.linearMap_ext fun p x hx ↦ ?_
  simp only [LinearMap.comp_apply]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [AA.grading.koszulTwist_apply_of_mem_zero hx]
  · rw [ε.map_of_mem_ne_zero p _ (AA.grading.koszulTwist_mem_piece hx q) hp,
      ε.map_of_mem_ne_zero p x hx hp]

private theorem map_reducedPart_map_subtype (ε : AA.Augmentation)
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    ReducedTensorWords.map (R := R) ε.reducedPart
      (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype w) = w := by
  rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
    show ε.reducedPart ∘ₗ ε.augmentationIdeal.subtype = LinearMap.id from
      LinearMap.ext ε.reducedPart_coe, ReducedTensorWords.map_id, LinearMap.id_apply]

private theorem multilinear_ext_of_split (ε : AA.Augmentation) {N : Type*}
    [AddCommGroup N] [Module R N] {n : ℕ}
    {M₁ M₂ : MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) N}
    (h : ∀ x : Fin n → A, (∀ i, x i = ε.unit ∨ x i ∈ ε.augmentationIdeal) → M₁ x = M₂ x) :
    M₁ = M₂ := by
  suffices hk : ∀ (k : ℕ) (x : Fin n → A),
      (∀ i : Fin n, k ≤ i.1 → x i = ε.unit ∨ x i ∈ ε.augmentationIdeal) → M₁ x = M₂ x from
    MultilinearMap.ext fun x ↦ hk n x fun i hi ↦ absurd i.isLt (by omega)
  intro k
  induction k with
  | zero => exact fun x hx ↦ h x fun i ↦ hx i (Nat.zero_le _)
  | succ k ih =>
    intro x hx
    by_cases hkn : k < n
    · let i₀ : Fin n := ⟨k, hkn⟩
      have hupd : Function.update x i₀ (ε (x i₀) • ε.unit + (ε.reducedPart (x i₀) : A)) = x := by
        funext i; rcases eq_or_ne i i₀ with rfl | hi
        · simp [coe_reducedPart]
        · exact Function.update_of_ne hi _ x
      have hmem (v : A) (hv : v = ε.unit ∨ v ∈ ε.augmentationIdeal) (i : Fin n) (_ : k ≤ i.1) :
          Function.update x i₀ v i = ε.unit ∨ Function.update x i₀ v i ∈ ε.augmentationIdeal := by
        rcases eq_or_ne i i₀ with rfl | hne
        · simpa using hv
        · rw [Function.update_of_ne hne]
          exact hx i (Nat.succ_le_of_lt (lt_of_le_of_ne ‹k ≤ i.1› fun h' ↦ hne (Fin.ext h'.symm)))
      rw [← hupd, M₁.map_update_add, M₂.map_update_add, M₁.map_update_smul, M₂.map_update_smul,
        ih _ (hmem _ (Or.inl rfl)), ih _ (hmem _ (Or.inr (ε.reducedPart (x i₀)).2))]
    · exact ih x fun i _ ↦ hx i (by omega)

private theorem linearMap_ext_of_split (ε : AA.Augmentation) {N : Type*}
    [AddCommGroup N] [Module R N] {L₁ L₂ : ReducedTensorWords R A →ₗ[R] N}
    (h : ∀ (n : {n : ℕ // 0 < n}) (x : Fin n.1 → A),
      (∀ i, x i = ε.unit ∨ x i ∈ ε.augmentationIdeal) →
      L₁ (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) =
        L₂ (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) :
    L₁ = L₂ :=
  ReducedTensorWords.linearMap_ext R A fun n x ↦
    MultilinearMap.congr_fun (ε.multilinear_ext_of_split
      (M₁ := (L₁ ∘ₗ ReducedTensorWords.of R A n).compMultilinearMap (PiTensorProduct.tprod R))
      (M₂ := (L₂ ∘ₗ ReducedTensorWords.of R A n).compMultilinearMap (PiTensorProduct.tprod R))
      (h n)) x

private noncomputable def augLetter (ε : AA.Augmentation) : ReducedTensorWords R A →ₗ[R] R :=
  ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A

/-- Cache the additive group structure on `ReducedTensorWords R ε.augmentationIdeal`. -/
local instance (ε : AA.Augmentation) :
    AddCommGroup (ReducedTensorWords R ε.augmentationIdeal) := inferInstance

/-- Cache the additive group structure on twofold tensor products of reduced words in `ker ε`. -/
local instance (ε : AA.Augmentation) :
    AddCommGroup (ReducedTensorWords R ε.augmentationIdeal ⊗[R]
      ReducedTensorWords R ε.augmentationIdeal) := inferInstance

private noncomputable def unitCut (ε : AA.Augmentation) :
    ReducedTensorWords R A ⊗[R] ReducedTensorWords R A →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal :=
  (TensorProduct.lid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
      TensorProduct.map (augLetter ε) (ReducedTensorWords.map (R := R) ε.reducedPart) -
    (TensorProduct.rid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
      TensorProduct.map (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
        (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1) (augLetter ε)

private theorem unitCut_tmul (ε : AA.Augmentation) (u v : ReducedTensorWords R A) :
    unitCut ε (u ⊗ₜ[R] v) =
      augLetter ε u • ReducedTensorWords.map (R := R) ε.reducedPart v -
        augLetter ε v • ReducedTensorWords.map (R := R) ε.reducedPart
          ((ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1 u) := by
  simp [unitCut]

private theorem unitCut_comp_map_subtype (ε : AA.Augmentation) :
    unitCut ε ∘ₗ TensorProduct.map (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype)
      (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype) = 0 :=
  TensorProduct.ext' fun u v ↦ by
    simp [unitCut_tmul, augLetter, letter_map_apply,
      (ε.mem_augmentationIdeal).mp (ReducedTensorWords.letter R _ u).2,
      (ε.mem_augmentationIdeal).mp (ReducedTensorWords.letter R _ v).2]

private theorem comp_taylor_eq_mul_deconcatenation (ε : AA.Augmentation) :
    ε.toLinearMap ∘ₗ AA.taylor =
      LinearMap.mul' R R ∘ₗ TensorProduct.map (augLetter ε) (augLetter ε) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  refine ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_
  rcases n with ⟨_ | _ | _ | k, hk⟩
  · omega
  · rw [ReducedTensorWords.of_tprod_eq_subword R hk x,
      ReducedTensorWords.subword_one R A x Nat.one_pos]
    simp [augLetter, ε.map_unary]
  · rw [ReducedTensorWords.of_tprod_eq_subword R hk x, ReducedTensorWords.subword_two_eq R x le_rfl]
    have htw := LinearMap.congr_fun (ε.comp_koszulTwist 1) (x 0)
    simp only [LinearMap.comp_apply] at htw
    simp [augLetter, AInfinityAlgebra.taylor_of_two, ReducedTensorWords.deconcatenation_of_two, htw]
  · rw [LinearMap.comp_apply, AInfinityAlgebra.taylor_of_tprod,
      show ε (AA.m (k + 3) _) = 0 from ε.map_m_of_ne_two (k + 3) hk (by omega) _,
      LinearMap.comp_apply, LinearMap.comp_apply, ReducedTensorWords.of_tprod_eq_subword R hk x,
      ReducedTensorWords.deconcatenation_subword, map_sum, map_sum]
    refine (Finset.sum_eq_zero fun c hc ↦ ?_).symm
    rw [Finset.mem_Ioo] at hc
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, augLetter, LinearMap.comp_apply]
    rcases eq_or_ne c 1 with rfl | hc1
    · rw [ReducedTensorWords.letter_subword_of_ne_one R A x (0 + 1) (by omega), map_zero, mul_zero]
    · rw [ReducedTensorWords.letter_subword_of_ne_one R A x 0 hc1, map_zero, zero_mul]

private theorem letter_comp_unitCut (ε : AA.Augmentation) (u v : ReducedTensorWords R A) :
    ReducedTensorWords.letter R ε.augmentationIdeal (unitCut ε (u ⊗ₜ[R] v)) =
      augLetter ε u • ε.reducedPart (ReducedTensorWords.letter R A v) +
        augLetter ε v •
          ε.reducedPart (AA.grading.koszulTwist 1 (ReducedTensorWords.letter R A u)) := by
  rw [unitCut_tmul, map_sub, map_smul, map_smul, letter_map_apply, letter_map_apply,
    ReducedTensorWords.koszulTwist_grading, letter_map_apply,
    InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply, map_neg, smul_neg,
    sub_neg_eq_add]

private theorem reducedPart_comp_taylor (ε : AA.Augmentation) :
    ε.reducedPart ∘ₗ AA.taylor =
      ε.reducedAlgebra.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
        ReducedTensorWords.letter R ε.augmentationIdeal ∘ₗ unitCut ε ∘ₗ
          ReducedTensorWords.deconcatenation R A := by
  refine ε.linearMap_ext_of_split fun n x hx ↦ ?_
  by_cases hunit : ∃ i, x i = ε.unit
  · obtain ⟨i₀, hi₀⟩ := hunit
    have hproj : ReducedTensorWords.map (R := R) ε.reducedPart
        (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) = 0 := by
      rw [ReducedTensorWords.map_of_tprod,
        (PiTensorProduct.tprod R).map_coord_zero i₀ (by rw [hi₀, ε.reducedPart_unit]), map_zero]
    rcases n with ⟨_ | _ | _ | k, hk⟩
    · omega
    · have hx0 : x ⟨0, hk⟩ = ε.unit := by fin_cases i₀; exact hi₀
      rw [ReducedTensorWords.of_tprod_eq_subword R hk x,
        ReducedTensorWords.subword_one R A x Nat.one_pos, hx0]
      simp [ε.isStrictUnit.unary_eq_zero]
    · simp only [LinearMap.add_apply, LinearMap.comp_apply, hproj, map_zero, zero_add]
      rw [ReducedTensorWords.of_tprod_eq_subword R hk x,
        ReducedTensorWords.subword_two_eq R x le_rfl]
      fin_cases i₀
      · have hi₀' : x ⟨0, by simp⟩ = ε.unit := hi₀
        rw [hi₀', ReducedTensorWords.deconcatenation_of_two, letter_comp_unitCut]
        simp [augLetter, ε.isStrictUnit.taylor_of_two_unit_left,
          AA.grading.koszulTwist_apply_of_mem_zero ε.isStrictUnit.degree_zero]
      · have hi₀' : x ⟨0 + 1, by simp⟩ = ε.unit := hi₀
        rw [hi₀', ReducedTensorWords.deconcatenation_of_two, letter_comp_unitCut]
        simp [augLetter, ε.isStrictUnit.taylor_of_two_unit_right]
    · rw [LinearMap.comp_apply,
        ε.isStrictUnit.taylor_of_tprod_eq_zero ⟨k + 3, hk⟩ (by simp) x ⟨i₀, hi₀⟩, map_zero,
        LinearMap.add_apply, LinearMap.comp_apply, hproj, map_zero, zero_add, LinearMap.comp_apply,
        LinearMap.comp_apply, ReducedTensorWords.of_tprod_eq_subword R hk x,
        ReducedTensorWords.deconcatenation_subword, map_sum, map_sum]
      refine (Finset.sum_eq_zero fun c hc ↦ ?_).symm
      rw [Finset.mem_Ioo] at hc; rw [letter_comp_unitCut]
      simp only [augLetter, LinearMap.comp_apply]
      rcases eq_or_ne c 1 with rfl | hc1
      · rw [ReducedTensorWords.letter_subword_of_ne_one R A x (0 + 1) (by omega), map_zero,
          smul_zero, zero_add, map_zero, zero_smul]
      · rw [ReducedTensorWords.letter_subword_of_ne_one R A x 0 hc1, map_zero, zero_smul, zero_add,
          map_zero, map_zero, smul_zero]
  · push Not at hunit
    let w := ReducedTensorWords.of R ε.augmentationIdeal n
      (PiTensorProduct.tprod R fun i ↦ ⟨x i, (hx i).resolve_left (hunit i)⟩)
    have hw : ReducedTensorWords.of R A n (PiTensorProduct.tprod R x) =
        ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype w := by
      rw [ReducedTensorWords.map_of_tprod]; rfl
    have huc : unitCut ε (ReducedTensorWords.deconcatenation R A
        (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype w)) = 0 := by
      rw [(ReducedTensorWords.isCoalgHom_map ε.augmentationIdeal.subtype).deconcatenation_apply,
        ← LinearMap.comp_apply (unitCut ε), ε.unitCut_comp_map_subtype, LinearMap.zero_apply]
    simp only [hw, LinearMap.add_apply, LinearMap.comp_apply, huc, map_zero, add_zero,
      ε.map_reducedPart_map_subtype, reducedAlgebra_taylor]

private theorem koszulTwist_comp_map_reducedPart (ε : AA.Augmentation) :
    (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 ∘ₗ
        ReducedTensorWords.map (R := R) ε.reducedPart =
      ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
        (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1 := by
  have hp : LinearMap.IsHomogeneous (ReducedTensorWords.map (R := R) ε.reducedPart)
      (ReducedTensorWords.grading (AA.grading.shift 1)).piece
      (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).piece 0 := by
    rw [ReducedTensorWords.grading_piece, ReducedTensorWords.grading_piece]
    exact ReducedTensorWords.isHomogeneous_map _ _
      (LinearMap.isHomogeneous_shift_piece_iff.mpr ε.isHomogeneous_reducedPart)
  simpa using hp.koszulTwist_comp_eq_smul 1

private theorem deconcatenation_unitCut_tmul (ε : AA.Augmentation) (u v : ReducedTensorWords R A) :
    ReducedTensorWords.deconcatenation R ε.augmentationIdeal (unitCut ε (u ⊗ₜ[R] v)) =
      augLetter ε u • TensorProduct.map (ReducedTensorWords.map (R := R) ε.reducedPart)
          (ReducedTensorWords.map (R := R) ε.reducedPart)
          (ReducedTensorWords.deconcatenation R A v) -
        augLetter ε v • TensorProduct.map
          (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
            (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
            (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          (ReducedTensorWords.deconcatenation R A u) := by
  rw [unitCut_tmul, map_sub, map_smul, map_smul,
    (ReducedTensorWords.isCoalgHom_map ε.reducedPart).deconcatenation_apply,
    (ReducedTensorWords.isCoalgHom_map ε.reducedPart).deconcatenation_apply,
    AA.isNonCounitalDGCoalgebra_bar.comul_koszulTwist,
    ← LinearMap.comp_apply (TensorProduct.map _ _) (TensorProduct.map _ _),
    ← TensorProduct.map_comp]

private theorem deconcatenation_comp_unitCut_comp_deconcatenation (ε : AA.Augmentation) :
    ReducedTensorWords.deconcatenation R ε.augmentationIdeal ∘ₗ unitCut ε ∘ₗ
        ReducedTensorWords.deconcatenation R A =
      (TensorProduct.map (unitCut ε ∘ₗ ReducedTensorWords.deconcatenation R A)
          (ReducedTensorWords.map (R := R) ε.reducedPart) +
        TensorProduct.map (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
          (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          (unitCut ε ∘ₗ ReducedTensorWords.deconcatenation R A)) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  let ΔA := ReducedTensorWords.deconcatenation R A
  let ΔI := ReducedTensorWords.deconcatenation R ε.augmentationIdeal
  let π := ReducedTensorWords.map (R := R) ε.reducedPart
  let σA := (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1
  let L := (TensorProduct.lid R _).toLinearMap ∘ₗ
      TensorProduct.map (augLetter ε) (TensorProduct.map π π) -
      TensorProduct.map (π ∘ₗ σA) (unitCut ε)
  let R_map := (TensorProduct.rid R _).toLinearMap ∘ₗ
      TensorProduct.map (TensorProduct.map (π ∘ₗ σA) (π ∘ₗ σA)) (augLetter ε) +
      TensorProduct.map (unitCut ε) π
  have hLR : L ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap = R_map :=
    TensorProduct.ext_threefold fun p q r ↦ by
      simp only [L, R_map, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, TensorProduct.assoc_tmul, TensorProduct.map_tmul,
        TensorProduct.lid_tmul, TensorProduct.rid_tmul, unitCut_tmul, TensorProduct.sub_tmul,
        TensorProduct.tmul_sub, TensorProduct.smul_tmul', TensorProduct.tmul_smul]; abel
  have hsplit : ΔI ∘ₗ unitCut ε -
      (TensorProduct.map (unitCut ε ∘ₗ ΔA) π + TensorProduct.map (π ∘ₗ σA) (unitCut ε ∘ₗ ΔA)) =
      L ∘ₗ ΔA.lTensor _ - R_map ∘ₗ ΔA.rTensor _ :=
    TensorProduct.ext' fun u v ↦ by
      simp only [L, R_map, ΔI, ΔA, π, σA, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
        TensorProduct.map_tmul, TensorProduct.lid_tmul, TensorProduct.rid_tmul,
        ε.deconcatenation_unitCut_tmul]; abel
  refine sub_eq_zero.mp (LinearMap.ext fun z ↦ ?_)
  have hz := LinearMap.congr_fun hsplit (ΔA z)
  have hco := LinearMap.congr_fun AA.isNonCounitalDGCoalgebra_bar.coassoc z
  simp only [ΔI, ΔA, π, σA, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.zero_apply] at hz hco ⊢
  rw [hz, ← hco, ← LinearMap.comp_apply L, hLR, sub_self]

private theorem deconcatenation_comp_barDifferential_error (ε : AA.Augmentation)
    (z : ReducedTensorWords R A) :
    let π := ReducedTensorWords.map (R := R) ε.reducedPart
    let σA := (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1
    let ΔA := ReducedTensorWords.deconcatenation R A
    let E := π ∘ₗ AA.barDifferential - (ε.reducedAlgebra.barDifferential ∘ₗ π + unitCut ε ∘ₗ ΔA)
    ReducedTensorWords.deconcatenation R ε.augmentationIdeal (E z) =
      (TensorProduct.map E π + TensorProduct.map (π ∘ₗ σA) E) (ΔA z) := by
  intro π σA ΔA E
  have h1 := LinearMap.congr_fun AA.isNonCounitalDGCoalgebra_bar.comul_differential z
  have h2 := LinearMap.congr_fun
    ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comul_differential (π z)
  have h3 := LinearMap.congr_fun ε.deconcatenation_comp_unitCut_comp_deconcatenation z
  simp only [LinearMap.comp_apply] at h1 h2 h3
  simp only [E, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sub, map_add]
  rw [(ReducedTensorWords.isCoalgHom_map ε.reducedPart).deconcatenation_apply, h1, h2,
    (ReducedTensorWords.isCoalgHom_map ε.reducedPart).deconcatenation_apply, h3]
  generalize ΔA z = w
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
    have htw := LinearMap.congr_fun ε.koszulTwist_comp_map_reducedPart u
    simp only [LinearMap.comp_apply] at htw
    simp only [π, σA, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.rTensor_tmul, TensorProduct.map_tmul, map_add, htw, TensorProduct.sub_tmul,
      TensorProduct.tmul_sub, TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
  | add _ _ hu hv => simp only [map_add] at hu hv ⊢; grind

private theorem map_reducedPart_comp_barDifferential (ε : AA.Augmentation) :
    ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ AA.barDifferential =
      ε.reducedAlgebra.barDifferential ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
        unitCut ε ∘ₗ ReducedTensorWords.deconcatenation R A := by
  let π := ReducedTensorWords.map (R := R) ε.reducedPart
  let ΔA := ReducedTensorWords.deconcatenation R A
  let E := π ∘ₗ AA.barDifferential - (ε.reducedAlgebra.barDifferential ∘ₗ π + unitCut ε ∘ₗ ΔA)
  have hletter : ReducedTensorWords.letter R ε.augmentationIdeal ∘ₗ E = 0 := by
    dsimp only [E, π, ΔA]
    rw [LinearMap.comp_sub, LinearMap.comp_add, ← LinearMap.comp_assoc,
      ReducedTensorWords.letter_comp_map, LinearMap.comp_assoc, AA.letter_comp_barDifferential,
      ← LinearMap.comp_assoc, ε.reducedAlgebra.letter_comp_barDifferential,
      ε.reducedPart_comp_taylor, sub_self]
  suffices hfil : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R A n, E z = 0 from
    sub_eq_zero.mp <| LinearMap.ext fun z ↦
      let ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R A z; hfil n z hn
  intro n; induction n with
  | zero =>
    intro z hz
    rw [ReducedTensorWords.filtration_zero] at hz
    rw [(Submodule.mem_bot R).mp hz, map_zero]
  | succ n ih =>
    intro z hz
    refine ReducedTensorWords.eq_of_deconcatenation_eq_of_letter_eq R ε.augmentationIdeal ?_
      (by simpa using LinearMap.congr_fun hletter z)
    obtain ⟨w, hw⟩ := ReducedTensorWords.map_deconcatenation_filtration_succ_le R A n ⟨z, hz, rfl⟩
    rw [map_zero, ε.deconcatenation_comp_barDifferential_error z, ← hw]
    clear hw; dsimp only [E, π, ΔA] at ih
    induction w using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [LinearMap.add_apply, TensorProduct.mapIncl, TensorProduct.map_tmul,
        Submodule.coe_subtype, ih u.1 u.2, ih v.1 v.2, TensorProduct.zero_tmul,
        TensorProduct.tmul_zero, add_zero]
    | add _ _ hu hv => simp only [map_add, hu, hv, add_zero]

end Single

end AInfinityAlgebra.Augmentation

namespace AInfinityHom.IsAugmented

variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {f : AInfinityHom AA BB} {εA : AA.Augmentation} {εB : BB.Augmentation}

/-- An augmented `A∞` morphism `(A, ε_A) ⟶ (B, ε_B)` restricts to an `A∞` morphism
`ker ε_A ⟶ ker ε_B` between reduced augmentation ideals. -/
noncomputable def reducedHom (hf : f.IsAugmented εA εB) :
    AInfinityHom εA.reducedAlgebra εB.reducedAlgebra :=
  εB.homToReducedEquiv εA.reducedAlgebra
    ⟨f.comp εA.inclusionStrictHom.toAInfinityHom, fun z ↦ by
      rw [AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
        AInfinityStrictHom.barMap_def, AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap,
        εB.mem_augmentationIdeal]
      have hz := LinearMap.congr_fun hf.comp_taylor
        (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype z)
      simp only [LinearMap.comp_apply, letter_map_apply] at hz
      exact hz.trans ((εA.mem_augmentationIdeal).mp (ReducedTensorWords.letter R _ z).2)⟩

/-- Postcomposing `hf.reducedHom` with the target inclusion equals `f` on the source inclusion. -/
theorem inclusionStrictHom_comp_reducedHom (hf : f.IsAugmented εA εB) :
    εB.inclusionStrictHom.toAInfinityHom.comp hf.reducedHom =
      f.comp εA.inclusionStrictHom.toAInfinityHom :=
  congrArg Subtype.val ((εB.homToReducedEquiv εA.reducedAlgebra).symm_apply_apply _)

/-- Explicit Taylor map of `hf.reducedHom`. -/
@[simp]
theorem taylor_reducedHom (hf : f.IsAugmented εA εB) :
    hf.reducedHom.taylor =
      εB.reducedPart ∘ₗ f.taylor ∘ₗ
        ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype := by
  simp [reducedHom, AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_def]

end AInfinityHom.IsAugmented

namespace AInfinityAlgebra.Augmentation

section Pair

variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  (εA : AA.Augmentation) (εB : BB.Augmentation)

private noncomputable def extendTaylor (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    ReducedTensorWords R A →ₗ[R] B :=
  εB.unitHom ∘ₗ augLetter εA +
    εB.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ ReducedTensorWords.map (R := R) εA.reducedPart

private theorem isHomogeneous_extendTaylor (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    LinearMap.IsHomogeneous (εA.extendTaylor εB g)
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
  refine (LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_).add ?_
  · rw [add_zero, LinearMap.comp_apply, augLetter, LinearMap.comp_apply, unitHom_apply]
    have hl : ReducedTensorWords.letter R A z ∈ AA.grading.piece (p + 1) := by
      simpa only [add_zero, InternalGrading.shift_piece] using
        (ReducedTensorWords.isHomogeneous_letter (AA.grading.shift 1)).map_mem hz
    rcases eq_or_ne (p + 1) 0 with hp | hp
    · obtain rfl : p = -1 := by omega
      exact Submodule.smul_mem _ _ εB.isStrictUnit.mem_shift_one_piece
    · rw [εA.map_of_mem_ne_zero (p + 1) _ hl hp, zero_smul]; exact zero_mem _
  · have hπA : LinearMap.IsHomogeneous (ReducedTensorWords.map (R := R) εA.reducedPart)
        (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
        (ReducedTensorWords.gradedPiece (εA.reducedAlgebra.grading.shift 1)) 0 :=
      ReducedTensorWords.isHomogeneous_map _ _
        (LinearMap.isHomogeneous_shift_piece_iff.mpr εA.isHomogeneous_reducedPart)
    have hsubB : LinearMap.IsHomogeneous εB.augmentationIdeal.subtype
        (εB.reducedAlgebra.grading.shift 1).piece (BB.grading.shift 1).piece 0 :=
      LinearMap.isHomogeneous_shift_piece_iff.mpr
        (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by simpa using hx)
    simpa only [add_zero] using hsubB.comp (g.isHomogeneous_taylor.comp hπA)

private theorem augLetter_comp_coalgHom_extendTaylor
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    augLetter εB ∘ₗ ReducedTensorWords.coalgHom R (εA.extendTaylor εB g) = augLetter εA := by
  rw [augLetter, LinearMap.comp_assoc, ReducedTensorWords.letter_comp_coalgHom]
  exact LinearMap.ext fun _ ↦ by
    simp [extendTaylor, augLetter, (εB.mem_augmentationIdeal).mp (g.taylor _).2]

private theorem map_reducedPart_comp_coalgHom_extendTaylor
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    ReducedTensorWords.map (R := R) εB.reducedPart ∘ₗ
        ReducedTensorWords.coalgHom R (εA.extendTaylor εB g) =
      g.barMap ∘ₗ ReducedTensorWords.map (R := R) εA.reducedPart := by
  rw [ReducedTensorWords.map_comp_coalgHom,
    show εB.reducedPart ∘ₗ εA.extendTaylor εB g =
      g.taylor ∘ₗ ReducedTensorWords.map (R := R) εA.reducedPart from
      LinearMap.ext fun _ ↦ by simp [extendTaylor],
    (g.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_map _)).eq_coalgHom,
    ← LinearMap.comp_assoc, ← g.taylor_def]

private theorem unitCut_comp_coalgHom_extendTaylor
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    unitCut εB ∘ₗ TensorProduct.map (ReducedTensorWords.coalgHom R (εA.extendTaylor εB g))
        (ReducedTensorWords.coalgHom R (εA.extendTaylor εB g)) =
      g.barMap ∘ₗ unitCut εA := by
  let F := ReducedTensorWords.coalgHom R (εA.extendTaylor εB g)
  have hF_hom : LinearMap.IsHomogeneous F (ReducedTensorWords.grading (AA.grading.shift 1)).piece
      (ReducedTensorWords.grading (BB.grading.shift 1)).piece 0 := by
    rw [ReducedTensorWords.grading_piece, ReducedTensorWords.grading_piece]
    exact ReducedTensorWords.isHomogeneous_coalgHom (εA.isHomogeneous_extendTaylor εB g)
  have hF_twist : (ReducedTensorWords.grading (BB.grading.shift 1)).koszulTwist 1 ∘ₗ F =
      F ∘ₗ (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1 := by
    simpa using hF_hom.koszulTwist_comp_eq_smul 1
  refine TensorProduct.ext' fun u v ↦ ?_
  simp only [F, LinearMap.comp_apply, TensorProduct.map_tmul, unitCut_tmul, map_sub, map_smul,
    ← LinearMap.comp_apply (augLetter εB), εA.augLetter_comp_coalgHom_extendTaylor εB g,
    ← LinearMap.comp_apply (ReducedTensorWords.map _ εB.reducedPart),
    εA.map_reducedPart_comp_coalgHom_extendTaylor εB g,
    ← LinearMap.comp_apply _ (ReducedTensorWords.coalgHom R _), hF_twist]

private theorem taylor_comp_coalgHom_extendTaylor
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    BB.taylor ∘ₗ ReducedTensorWords.coalgHom R (εA.extendTaylor εB g) =
      εA.extendTaylor εB g ∘ₗ AA.barDifferential := by
  let ft := εA.extendTaylor εB g
  let F := ReducedTensorWords.coalgHom R ft
  have hε_ft : εB.toLinearMap ∘ₗ ft = augLetter εA := LinearMap.ext fun _ ↦ by
    simp [ft, extendTaylor, augLetter, (εB.mem_augmentationIdeal).mp (g.taylor _).2]
  have hπ_ft : εB.reducedPart ∘ₗ ft = g.taylor ∘ₗ ReducedTensorWords.map (R := R) εA.reducedPart :=
    LinearMap.ext fun _ ↦ by simp [ft, extendTaylor]
  have haug_F := εA.augLetter_comp_coalgHom_extendTaylor εB g
  refine LinearMap.ext fun z ↦ (εB.eq_iff_map_eq_and_reducedPart_eq).mpr ⟨?_, ?_⟩
  · have h1 := LinearMap.congr_fun εB.comp_taylor_eq_mul_deconcatenation (F z)
    have h2 := LinearMap.congr_fun εA.comp_taylor_eq_mul_deconcatenation z
    have h3 := LinearMap.congr_fun hε_ft (AA.barDifferential z)
    simp only [F, ft, augLetter, LinearMap.comp_apply] at h1 h2 h3 haug_F ⊢
    rw [h1, (ReducedTensorWords.isCoalgHom_coalgHom _).deconcatenation_apply,
      ← LinearMap.comp_apply (TensorProduct.map _ _) (TensorProduct.map _ _),
      ← TensorProduct.map_comp, haug_F, h3,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R A) AA.barDifferential,
      AA.letter_comp_barDifferential]
    exact h2.symm
  · have h1 := LinearMap.congr_fun εB.reducedPart_comp_taylor (F z)
    have h2 := LinearMap.congr_fun hπ_ft (AA.barDifferential z)
    have h3 := LinearMap.congr_fun εA.map_reducedPart_comp_barDifferential z
    simp only [F, ft, LinearMap.comp_apply, LinearMap.add_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3, map_add,
      ← LinearMap.comp_apply (ReducedTensorWords.map _ εB.reducedPart),
      εA.map_reducedPart_comp_coalgHom_extendTaylor εB g, LinearMap.comp_apply,
      ← LinearMap.comp_apply εB.reducedAlgebra.taylor g.barMap, g.taylor_comp_barMap,
      LinearMap.comp_apply, (ReducedTensorWords.isCoalgHom_coalgHom _).deconcatenation_apply,
      ← LinearMap.comp_apply (unitCut εB) (TensorProduct.map _ _),
      εA.unitCut_comp_coalgHom_extendTaylor εB g, LinearMap.comp_apply,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R _) g.barMap, ← g.taylor_def]

/-- Extend any `A∞` morphism `g : ker ε_A ⟶ ker ε_B` to a strictly unital `A∞` morphism `A ⟶ B`. -/
noncomputable def extendHom (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    AInfinityHom AA BB :=
  AInfinityHom.ofTaylor (εA.extendTaylor εB g) (εA.isHomogeneous_extendTaylor εB g)
    (εA.taylor_comp_coalgHom_extendTaylor εB g)

/-- Explicit formula for the Taylor map of `extendHom`. -/
@[simp]
theorem taylor_extendHom (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    (εA.extendHom εB g).taylor =
      εB.unitHom ∘ₗ εA.toLinearMap ∘ₗ ReducedTensorWords.letter R A +
        εB.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ
          ReducedTensorWords.map (R := R) εA.reducedPart := by
  simp [extendHom, extendTaylor, augLetter]

/-- The extended morphism `extendHom` is strictly unital and augmented. -/
theorem isAugmented_extendHom (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    (εA.extendHom εB g).IsAugmented εA εB where
  isStrictlyUnital := by
    refine ⟨by simp [AInfinityHom.linearPart_apply, taylor_extendHom], fun {n} hn x ⟨i, hi⟩ ↦ ?_⟩
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hnpos := Nat.pos_of_ne_zero hn0
      have hne1 : (⟨n, hnpos⟩ : {k : ℕ // 0 < k}) ≠ 1 :=
        fun h ↦ hn (by simpa using congrArg Subtype.val h)
      have hyi : εA.reducedPart (AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)) = 0 := by
        rw [hi, AA.grading.koszulTwist_apply_of_mem_zero εA.isStrictUnit.degree_zero,
          εA.reducedPart_unit]
      have hproj : ReducedTensorWords.map (R := R) εA.reducedPart
          (ReducedTensorWords.of R A ⟨n, hnpos⟩ (PiTensorProduct.tprod R fun j ↦
            AA.grading.koszulTwist ((n : ℤ) - 1 - j) (x j))) = 0 := by
        rw [ReducedTensorWords.map_of_tprod, (PiTensorProduct.tprod R).map_coord_zero i hyi,
          map_zero]
      rw [AInfinityHom.component_apply _ n hnpos, taylor_extendHom]
      simp [ReducedTensorWords.letter_of_of_ne_one R A hne1, hproj]
  comp_taylor := LinearMap.ext fun _ ↦ by
    simp [taylor_extendHom, (εB.mem_augmentationIdeal).mp (g.taylor _).2]

private theorem extendHom_reducedHom {f : AInfinityHom AA BB} (hf : f.IsAugmented εA εB) :
    εA.extendHom εB hf.reducedHom = f := by
  apply AInfinityHom.ext
  have hπ : εB.reducedPart ∘ₗ (εA.extendHom εB hf.reducedHom).taylor =
      εB.reducedPart ∘ₗ f.taylor := by
    refine εA.linearMap_ext_of_split fun n x hx ↦ ?_
    simp only [LinearMap.comp_apply, taylor_extendHom, LinearMap.add_apply,
      AInfinityHom.IsAugmented.taylor_reducedHom]
    by_cases hunit : ∃ i, x i = εA.unit
    · obtain ⟨i₀, hi₀⟩ := hunit
      have hproj : ReducedTensorWords.map (R := R) εA.reducedPart
          (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) = 0 := by
        rw [ReducedTensorWords.map_of_tprod,
          (PiTensorProduct.tprod R).map_coord_zero i₀ (by rw [hi₀, εA.reducedPart_unit]), map_zero]
      simp only [hproj, map_zero, add_zero, unitHom_apply, map_smul, εB.reducedPart_unit, smul_zero]
      obtain ⟨k, hk⟩ := n
      rcases eq_or_ne k 1 with rfl | hn1
      · fin_cases i₀
        rw [ReducedTensorWords.of_tprod_eq_subword R hk x,
          ReducedTensorWords.subword_one R A x Nat.one_pos, hi₀, ← f.linearPart_apply,
          hf.isStrictlyUnital.map_unit, εB.reducedPart_unit]
      · rw [hf.isStrictlyUnital.taylor_of_tprod_eq_zero ⟨k, hk⟩ hn1 x ⟨i₀, hi₀⟩, map_zero]
    · push Not at hunit
      let w := ReducedTensorWords.of R εA.augmentationIdeal n
        (PiTensorProduct.tprod R fun i ↦ ⟨x i, (hx i).resolve_left (hunit i)⟩)
      have hw : ReducedTensorWords.of R A n (PiTensorProduct.tprod R x) =
          ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w := by
        rw [ReducedTensorWords.map_of_tprod]; rfl
      rw [hw, εA.map_reducedPart_map_subtype]; simp [unitHom_apply, εB.reducedPart_unit]
  exact LinearMap.ext fun z ↦ (εB.eq_iff_map_eq_and_reducedPart_eq).mpr
    ⟨(LinearMap.congr_fun (εA.isAugmented_extendHom εB hf.reducedHom).comp_taylor z).trans
      (LinearMap.congr_fun hf.comp_taylor z).symm, LinearMap.congr_fun hπ z⟩

/-- **Equivalence between augmented `A∞` morphisms and reduced `A∞` morphisms**: strictly unital
augmented `A∞` morphisms `(A, ε_A) ⟶ (B, ε_B)` correspond bijectively to `A∞` morphisms
`ker ε_A ⟶ ker ε_B` between their reduced augmentation ideals. -/
noncomputable def augmentedHomEquiv :
    {f : AInfinityHom AA BB // f.IsAugmented εA εB} ≃
      AInfinityHom εA.reducedAlgebra εB.reducedAlgebra where
  toFun f := f.2.reducedHom
  invFun g := ⟨εA.extendHom εB g, εA.isAugmented_extendHom εB g⟩
  left_inv f := Subtype.ext (εA.extendHom_reducedHom εB f.2)
  right_inv g := AInfinityHom.ext <| LinearMap.ext fun z ↦ by
    simp [AInfinityHom.IsAugmented.taylor_reducedHom, taylor_extendHom,
      εA.map_reducedPart_map_subtype, letter_map_apply,
      (εA.mem_augmentationIdeal).mp (ReducedTensorWords.letter R _ z).2]

/-- Explicit Taylor map of `augmentedHomEquiv εB f`. -/
@[simp]
theorem taylor_augmentedHomEquiv_apply (f : {f : AInfinityHom AA BB // f.IsAugmented εA εB}) :
    (εA.augmentedHomEquiv εB f).taylor =
      εB.reducedPart ∘ₗ f.1.taylor ∘ₗ
        ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype :=
  f.2.taylor_reducedHom

/-- Explicit Taylor map of `(augmentedHomEquiv εB).symm g`. -/
@[simp]
theorem taylor_augmentedHomEquiv_symm_apply
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    ((εA.augmentedHomEquiv εB).symm g).1.taylor =
      εB.unitHom ∘ₗ εA.toLinearMap ∘ₗ ReducedTensorWords.letter R A +
        εB.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ
          ReducedTensorWords.map (R := R) εA.reducedPart :=
  εA.taylor_extendHom εB g

/-- Passing to the reduced morphism preserves composition of augmented `A∞` morphisms. -/
@[simp]
theorem augmentedHomEquiv_comp {C : Type uC} [AddCommGroup C] [Module R C]
    {CC : AInfinityAlgebra R C} {εC : CC.Augmentation}
    (g : {g : AInfinityHom BB CC // g.IsAugmented εB εC})
    (f : {f : AInfinityHom AA BB // f.IsAugmented εA εB}) :
    εA.augmentedHomEquiv εC ⟨g.1.comp f.1, g.2.comp f.2⟩ =
      (εB.augmentedHomEquiv εC g).comp (εA.augmentedHomEquiv εB f) := by
  simp only [augmentedHomEquiv, Equiv.coe_fn_mk, AInfinityHom.IsAugmented.reducedHom]
  rw [← εC.homToReducedEquiv_comp εA.reducedAlgebra εB.reducedAlgebra]
  refine congrArg (εC.homToReducedEquiv εA.reducedAlgebra) (Subtype.ext ?_)
  dsimp only
  conv_lhs =>
    rw [AInfinityHom.comp_assoc, ← f.2.inclusionStrictHom_comp_reducedHom,
      ← AInfinityHom.comp_assoc]
  rfl

end Pair

/-- Passing to the reduced morphism preserves identity morphisms. -/
@[simp]
theorem augmentedHomEquiv_id {A : Type uA} [AddCommGroup A] [Module R A]
    {AA : AInfinityAlgebra R A} (εA : AA.Augmentation) :
    εA.augmentedHomEquiv εA ⟨AInfinityHom.id AA, AInfinityHom.isAugmented_id εA⟩ =
      AInfinityHom.id εA.reducedAlgebra :=
  AInfinityHom.ext <| LinearMap.ext fun _ ↦ by simp [taylor_augmentedHomEquiv_apply]

end AInfinityAlgebra.Augmentation

end Splitting

section DGAugmentation

variable {R : Type uR} [CommRing R]

namespace DGAlgAugmentation

variable {A : Type uA} [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} (eA : DGAlgAugmentation hA)

/-- A DG algebra augmentation induces an augmentation of its associated `A∞` algebra. -/
noncomputable def toAInfinityAugmentation :
    hA.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.Augmentation where
  unit := 1
  isStrictUnit := hA.strictUnit_one
  toLinearMap := eA.toGradedAlgHom.toAlgHom.toLinearMap
  map_unit := by simp
  map_of_mem_ne_zero p x hx hp := by
    rcases (mem_trivialGrading_iff R R).mp (eA.map_mem (by simpa using hx)) with rfl | h0
    · exact absurd rfl hp
    · exact h0
  map_binary _ _ := by simp
  map_m_of_ne_two n _ hn2 _ := by
    rcases n with _ | _ | _ | k
    · omega
    · simp [eA.map_d]
    · exact absurd rfl hn2
    · simp

/-- The strict unit of `eA.toAInfinityAugmentation` is `1`. -/
@[simp]
theorem toAInfinityAugmentation_unit : eA.toAInfinityAugmentation.unit = 1 := (rfl)

/-- Evaluating `eA.toAInfinityAugmentation` agrees with `eA`. -/
@[simp]
theorem toAInfinityAugmentation_apply (a : A) : eA.toAInfinityAugmentation a = eA a := (rfl)

/-- The augmentation ideal of `toAInfinityAugmentation` is `eA.augmentationIdeal.toSubmodule`. -/
@[simp]
theorem toAInfinityAugmentation_augmentationIdeal :
    eA.toAInfinityAugmentation.augmentationIdeal = eA.augmentationIdeal.toSubmodule := by
  ext a
  exact (eA.toAInfinityAugmentation.mem_augmentationIdeal).trans eA.mem_augmentationIdeal.symm

end DGAlgAugmentation

namespace DGAlgHom

variable {A : Type uA} {B : Type uB}
  [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

/-- A DG algebra morphism induces an augmented `A∞` morphism iff it commutes with augmentations. -/
@[simp]
theorem isAugmented_toAInfinityHom_iff (eA : DGAlgAugmentation hA) (eB : DGAlgAugmentation hB)
    (φ : DGAlgHom hA hB) :
    φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsAugmented
        eA.toAInfinityAugmentation eB.toAInfinityAugmentation ↔ eB.comp φ = eA := by
  rw [(AInfinityHom.isStrict_toAInfinityHom _).isAugmented_iff]
  refine ⟨fun ⟨_, hlin⟩ ↦ ?_, fun h ↦ ⟨by simp, LinearMap.ext fun a ↦ ?_⟩⟩
  · ext a; simpa using LinearMap.congr_fun hlin a
  · simpa using DFunLike.congr_fun h a

end DGAlgHom

end DGAugmentation

end TauCeti
