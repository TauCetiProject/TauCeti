/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.Normed.Algebra.Character.Unitization

/-!
# Gelfand duality for nonunital commutative C⋆-algebras

For a nonunital commutative complex C⋆-algebra `A` (with no separability or nontriviality
assumption), this file establishes nonunital Gelfand duality both via the minimal C⋆-unitization
`Unitization ℂ A` and intrinsically on `characterSpace ℂ A`:

1. Every nonunital complex character of a (not necessarily commutative) `NonUnitalCStarAlgebra A`
   is automatically `⋆`-preserving (`WeakDual.Complex.instNonUnitalStarHomClass` and
   `WeakDual.CharacterSpace.instNonUnitalStarHomClass`).
2. Writing `ε := WeakDual.CharacterSpace.fstCharacter ℂ A` for the scalar-projection character on
   `Unitization ℂ A` and `K := characterSpace ℂ (Unitization ℂ A)`, the canonical inclusion
   identifies `A` isometrically and `⋆`-isomorphically with the closed two-sided ideal
   `TwoSidedIdeal.ker ε` (`Unitization.inrKerEquiv`).
3. When `A` is commutative, `gelfandStarTransform (Unitization ℂ A)` restricts to an isometric
   `⋆`-isomorphism from `TwoSidedIdeal.ker ε` onto
   `TwoSidedIdeal.ker (ContinuousMap.evalStarAlgHom ℂ ℂ ε)` (`TauCeti.gelfandKerFstCharacterEquiv`),
   and restriction to the punctured locally compact Hausdorff space `X := ({ε}ᶜ : Set K)` with
   inverse extension by zero gives an isometric `⋆`-isomorphism onto `C₀(X, ℂ)`
   (`ContinuousMap.kerEvalStarAlgHomEquivZeroAtInfty`, `TauCeti.puncturedGelfandStarTransform`).
4. Transporting along `WeakDual.CharacterSpace.homeoComplFstCharacter ℂ A` proves that
   `WeakDual.nonUnitalGelfandTransform ℂ A` is a bijective isometry onto
   `C₀(characterSpace ℂ A, ℂ)`, yielding the intrinsic `⋆`-isomorphism
   `TauCeti.nonUnitalGelfandStarTransform A : A ≃⋆ₐ[ℂ] C₀(characterSpace ℂ A, ℂ)`.
5. Both degenerate and unital cases are covered without side hypotheses: when `[Subsingleton A]`,
   `K` is a singleton and `X` and `characterSpace ℂ A` are empty so both `C₀` targets are
   subsingletons; a commutative C⋆-algebra `A` admits a multiplicative identity if and only if
   `characterSpace ℂ A` is compact (equivalently, `{ε}` is open in `K`), and for a unital
   `CommCStarAlgebra B` the nonunital equivalences agree with `gelfandStarTransform B` via
   `ContinuousMap.liftZeroAtInftyStarAlgEquiv`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, §II.2.2.
* G. J. Murphy, *C*-Algebras and Operator Theory*, Theorem 2.1.10 and §2.2.
* Built on Mathlib's unital Gelfand duality (`gelfandStarTransform`,
  `gelfandTransform_isometry`, `gelfandTransform_bijective` in
  `Mathlib.Analysis.CStarAlgebra.GelfandDuality`, by Jireh Loreaux) and
  `WeakDual.Complex.instStarHomClass` (`Mathlib.Analysis.CStarAlgebra.Spectrum`).
-/

public section

open Filter Topology WeakDual
open scoped ZeroAtInfty

namespace WeakDual

section NonUnitalStarHomClass

variable {F A : Type*} [NonUnitalCStarAlgebra A] [FunLike F A ℂ] [NonUnitalAlgHomClass F ℂ A ℂ]

/-- Every nonunital algebra homomorphism from a C⋆-algebra into `ℂ` preserves the involution. -/
noncomputable instance (priority := 100) Complex.instNonUnitalStarHomClass :
    StarHomClass F A ℂ where
  map_star φ a := by
    let ψ : Unitization ℂ A →ₐ[ℂ] ℂ :=
      Unitization.lift (NonUnitalAlgHomClass.toNonUnitalAlgHom φ)
    have hψ : NonUnitalAlgHomClass.toNonUnitalAlgHom φ (star a) =
        star (NonUnitalAlgHomClass.toNonUnitalAlgHom φ a) := by
      simpa [ψ, ← Unitization.inr_star] using map_star ψ (a : Unitization ℂ A)
    exact hψ

/-- Non-instance form of `WeakDual.Complex.instNonUnitalStarHomClass`, mirroring
`AlgHomClass.instStarHomClass`. -/
lemma _root_.NonUnitalAlgHomClass.instStarHomClass : StarHomClass F A ℂ :=
  WeakDual.Complex.instNonUnitalStarHomClass

namespace CharacterSpace

noncomputable instance instNonUnitalStarHomClass : StarHomClass (characterSpace ℂ A) A ℂ :=
  NonUnitalAlgHomClass.instStarHomClass

end CharacterSpace

end NonUnitalStarHomClass

namespace CharacterSpace

section UnitalCStar

variable (B : Type*) [CStarAlgebra B]

/-- For a unital C⋆-algebra `B`, `{fstCharacter ℂ B}` is clopen in
`characterSpace ℂ (Unitization ℂ B)`. -/
theorem isClopen_singleton_fstCharacter :
    IsClopen ({fstCharacter ℂ B} : Set (characterSpace ℂ (Unitization ℂ B))) :=
  isClopen_singleton_fstCharacter_of_forall_mul_eq (e := (1 : B)) one_mul

/-- For a unital C⋆-algebra `B`, `fstCharacter ℂ B` is isolated in
`characterSpace ℂ (Unitization ℂ B)`. -/
theorem isOpen_singleton_fstCharacter :
    IsOpen ({fstCharacter ℂ B} : Set (characterSpace ℂ (Unitization ℂ B))) :=
  (isClopen_singleton_fstCharacter B).2

/-- For a unital C⋆-algebra `B`, the punctured character space `{fstCharacter ℂ B}ᶜ` is compact. -/
instance instCompactSpaceComplFstCharacter :
    CompactSpace ({fstCharacter ℂ B}ᶜ : Set (characterSpace ℂ (Unitization ℂ B))) :=
  (TauCeti.isOpen_singleton_iff_compactSpace_compl (fstCharacter ℂ B)).mp
    (isOpen_singleton_fstCharacter B)

end UnitalCStar

end CharacterSpace

end WeakDual

namespace Unitization

variable (A : Type*) [NonUnitalCStarAlgebra A]

/-- As sets in `Unitization ℂ A`, the kernel of `fstCharacter ℂ A` is the range of the canonical
inclusion `A → Unitization ℂ A`. -/
theorem coe_ker_fstCharacter :
    (TwoSidedIdeal.ker (CharacterSpace.fstCharacter ℂ A) : Set (Unitization ℂ A)) =
      Set.range ((↑) : A → Unitization ℂ A) := by
  ext x
  rw [SetLike.mem_coe, CharacterSpace.mem_ker_fstCharacter, Set.mem_range]
  refine ⟨fun hx => ⟨x.snd, Unitization.ext (hx.trans (fst_inr ℂ x.snd).symm).symm rfl⟩, ?_⟩
  rintro ⟨a, rfl⟩
  exact fst_inr ℂ a

/-- A nonunital C⋆-algebra `A` is `⋆`-isomorphic (hence isometric) to the closed two-sided ideal
`TwoSidedIdeal.ker (CharacterSpace.fstCharacter ℂ A)` inside `Unitization ℂ A`. -/
noncomputable def inrKerEquiv :
    A ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (CharacterSpace.fstCharacter ℂ A) where
  toFun a := ⟨(a : Unitization ℂ A), by simp⟩
  invFun x := x.1.snd
  left_inv a := snd_inr ℂ a
  right_inv x := Subtype.ext <|
    Unitization.ext (by simp [CharacterSpace.mem_ker_fstCharacter.mp x.2]) rfl
  map_smul' c a := Subtype.ext (inr_smul ℂ c a)
  map_add' a b := Subtype.ext (inr_add ℂ a b)
  map_mul' a b := Subtype.ext (inr_mul ℂ a b)
  map_star' a := Subtype.ext (inr_star a)

@[simp]
theorem inrKerEquiv_apply_coe (a : A) :
    (inrKerEquiv A a : Unitization ℂ A) = a := (rfl)

@[simp]
theorem inrKerEquiv_symm_apply (x : TwoSidedIdeal.ker (CharacterSpace.fstCharacter ℂ A)) :
    (inrKerEquiv A).symm x = x.1.snd := (rfl)

theorem norm_inrKerEquiv (a : A) : ‖inrKerEquiv A a‖ = ‖a‖ :=
  StarAlgEquiv.norm_map (inrKerEquiv A) a

end Unitization

namespace ContinuousMap

variable {K : Type*} [TopologicalSpace K]

@[simp]
theorem mem_ker_evalStarAlgHom {S R : Type*} [CommSemiring S] [CommRing R] [Algebra S R]
    [TopologicalSpace R] [IsTopologicalRing R] [StarRing R] [ContinuousStar R]
    {x₀ : K} {F : C(K, R)} :
    F ∈ TwoSidedIdeal.ker (evalStarAlgHom S R x₀) ↔ F x₀ = 0 :=
  TwoSidedIdeal.mem_ker _

variable [CompactSpace K] [T2Space K]

/-- On a compact Hausdorff space `K`, restricting functions in `{F ∈ C(K, R) : F x₀ = 0}` to
`{x₀}ᶜ` defines an isometric `⋆`-isomorphism onto `C₀(({x₀}ᶜ : Set K), R)`, with inverse given by
extension by zero at `x₀`. -/
noncomputable def kerEvalStarAlgHomEquivZeroAtInfty (R : Type*) [CommCStarAlgebra R] (x₀ : K) :
    TwoSidedIdeal.ker (evalStarAlgHom ℂ R x₀) ≃⋆ₐ[ℂ] C₀(({x₀}ᶜ : Set K), R) where
  toFun F := F.1.restrictComplSingleton (mem_ker_evalStarAlgHom.mp F.2)
  invFun f := ⟨f.extendComplSingleton, mem_ker_evalStarAlgHom.mpr f.extendComplSingleton_apply_self⟩
  left_inv F := Subtype.ext <|
    F.1.extendComplSingleton_restrictComplSingleton (mem_ker_evalStarAlgHom.mp F.2)
  right_inv f := f.restrictComplSingleton_extendComplSingleton
  map_smul' c F := by ext y; simp
  map_add' F G := by ext y; simp
  map_mul' F G := by ext y; simp
  map_star' F := by ext y; simp

@[simp]
theorem kerEvalStarAlgHomEquivZeroAtInfty_apply {R : Type*} [CommCStarAlgebra R] (x₀ : K)
    (F : TwoSidedIdeal.ker (evalStarAlgHom ℂ R x₀)) (y : ({x₀}ᶜ : Set K)) :
    kerEvalStarAlgHomEquivZeroAtInfty R x₀ F y = F.1 y := by
  simp [kerEvalStarAlgHomEquivZeroAtInfty]

@[simp]
theorem kerEvalStarAlgHomEquivZeroAtInfty_symm_apply_coe {R : Type*} [CommCStarAlgebra R] (x₀ : K)
    (f : C₀(({x₀}ᶜ : Set K), R)) :
    ((kerEvalStarAlgHomEquivZeroAtInfty R x₀).symm f : C(K, R)) = f.extendComplSingleton := (rfl)

@[simp]
theorem norm_kerEvalStarAlgHomEquivZeroAtInfty {R : Type*} [CommCStarAlgebra R] (x₀ : K)
    (F : TwoSidedIdeal.ker (evalStarAlgHom ℂ R x₀)) :
    ‖kerEvalStarAlgHomEquivZeroAtInfty R x₀ F‖ = ‖F‖ :=
  StarAlgEquiv.norm_map (kerEvalStarAlgHomEquivZeroAtInfty R x₀) F

end ContinuousMap

namespace TauCeti

section NonUnitalCommCStarAlgebra

variable (A : Type*) [NonUnitalCommCStarAlgebra A]

/-- The unital Gelfand `⋆`-isomorphism of `Unitization ℂ A` restricts to a `⋆`-isomorphism between
`TwoSidedIdeal.ker (CharacterSpace.fstCharacter ℂ A)` and the vanishing ideal
`TwoSidedIdeal.ker (ContinuousMap.evalStarAlgHom ℂ ℂ (CharacterSpace.fstCharacter ℂ A))`. -/
noncomputable def gelfandKerFstCharacterEquiv :
    TwoSidedIdeal.ker (CharacterSpace.fstCharacter ℂ A) ≃⋆ₐ[ℂ]
      TwoSidedIdeal.ker
        (ContinuousMap.evalStarAlgHom ℂ ℂ (CharacterSpace.fstCharacter ℂ A)) where
  toFun x := ⟨gelfandStarTransform (Unitization ℂ A) x.1, by
    rw [ContinuousMap.mem_ker_evalStarAlgHom]
    simpa using TwoSidedIdeal.mem_ker _ |>.mp x.2⟩
  invFun F := ⟨(gelfandStarTransform (Unitization ℂ A)).symm F.1, by
    rw [CharacterSpace.mem_ker_fstCharacter]
    have hF : F.1 (CharacterSpace.fstCharacter ℂ A) = 0 :=
      ContinuousMap.mem_ker_evalStarAlgHom.mp F.2
    have hsymm :=
      DFunLike.congr_fun ((gelfandStarTransform (Unitization ℂ A)).apply_symm_apply F.1)
        (CharacterSpace.fstCharacter ℂ A)
    simpa [hF] using hsymm⟩
  left_inv x := Subtype.ext ((gelfandStarTransform (Unitization ℂ A)).symm_apply_apply x.1)
  right_inv F := Subtype.ext ((gelfandStarTransform (Unitization ℂ A)).apply_symm_apply F.1)
  map_smul' c x := Subtype.ext (map_smul (gelfandStarTransform (Unitization ℂ A)) c x.1)
  map_add' x y := Subtype.ext (map_add (gelfandStarTransform (Unitization ℂ A)) x.1 y.1)
  map_mul' x y := Subtype.ext (map_mul (gelfandStarTransform (Unitization ℂ A)) x.1 y.1)
  map_star' x := Subtype.ext (map_star (gelfandStarTransform (Unitization ℂ A)) x.1)

@[simp]
theorem gelfandKerFstCharacterEquiv_apply_coe
    (x : TwoSidedIdeal.ker (CharacterSpace.fstCharacter ℂ A)) :
    (gelfandKerFstCharacterEquiv A x : C(characterSpace ℂ (Unitization ℂ A), ℂ)) =
      gelfandStarTransform (Unitization ℂ A) x.1 := (rfl)

@[simp]
theorem gelfandKerFstCharacterEquiv_symm_apply_coe
    (F : TwoSidedIdeal.ker
      (ContinuousMap.evalStarAlgHom ℂ ℂ (CharacterSpace.fstCharacter ℂ A))) :
    ((gelfandKerFstCharacterEquiv A).symm F : Unitization ℂ A) =
      (gelfandStarTransform (Unitization ℂ A)).symm F.1 := (rfl)

/-- **Unitized nonunital Gelfand `⋆`-isomorphism**: a nonunital commutative C⋆-algebra `A` is
isometrically `⋆`-isomorphic to `C₀(K \ {ε}, ℂ)`, where `K = characterSpace ℂ (Unitization ℂ A)`
and `ε = CharacterSpace.fstCharacter ℂ A`, with inverse given by zero-extension to `K` followed by
`(gelfandStarTransform (Unitization ℂ A)).symm` and projection onto `A`. -/
noncomputable def puncturedGelfandStarTransform :
    A ≃⋆ₐ[ℂ]
      C₀(({CharacterSpace.fstCharacter ℂ A}ᶜ : Set (characterSpace ℂ (Unitization ℂ A))), ℂ) :=
  (Unitization.inrKerEquiv A).trans <|
    (gelfandKerFstCharacterEquiv A).trans <|
      ContinuousMap.kerEvalStarAlgHomEquivZeroAtInfty ℂ (CharacterSpace.fstCharacter ℂ A)

@[simp]
theorem puncturedGelfandStarTransform_apply (a : A)
    (χ : ({CharacterSpace.fstCharacter ℂ A}ᶜ : Set (characterSpace ℂ (Unitization ℂ A)))) :
    puncturedGelfandStarTransform A a χ = χ.1 (a : Unitization ℂ A) := by
  simp [puncturedGelfandStarTransform]

@[simp]
theorem inr_puncturedGelfandStarTransform_symm
    (f : C₀(({CharacterSpace.fstCharacter ℂ A}ᶜ : Set (characterSpace ℂ (Unitization ℂ A))), ℂ)) :
    ((puncturedGelfandStarTransform A).symm f : Unitization ℂ A) =
      (gelfandStarTransform (Unitization ℂ A)).symm f.extendComplSingleton := by
  have hx :=
    (Unitization.inrKerEquiv A).apply_symm_apply
      ((gelfandKerFstCharacterEquiv A).symm
        ((ContinuousMap.kerEvalStarAlgHomEquivZeroAtInfty ℂ
          (CharacterSpace.fstCharacter ℂ A)).symm f))
  simpa [puncturedGelfandStarTransform] using congrArg Subtype.val hx

@[simp]
theorem norm_puncturedGelfandStarTransform (a : A) :
    ‖puncturedGelfandStarTransform A a‖ = ‖a‖ :=
  StarAlgEquiv.norm_map (puncturedGelfandStarTransform A) a

theorem puncturedGelfandStarTransform_isometry :
    Isometry (puncturedGelfandStarTransform A) :=
  StarAlgEquiv.isometry (puncturedGelfandStarTransform A)

variable {A} in
theorem nonUnitalGelfandTransform_map_star (a : A) :
    nonUnitalGelfandTransform ℂ A (star a) = star (nonUnitalGelfandTransform ℂ A a) := by
  ext φ
  simp [map_star]

/-- Reindexing `puncturedGelfandStarTransform A` along `(homeoComplFstCharacter ℂ A).symm` gives
`nonUnitalGelfandTransform ℂ A`. -/
theorem congrLeftStarAlgEquiv_puncturedGelfandStarTransform_apply (a : A) :
    ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ ℂ
        (CharacterSpace.homeoComplFstCharacter ℂ A).symm
        (puncturedGelfandStarTransform A a) =
      nonUnitalGelfandTransform ℂ A a := by
  ext φ
  simp

private theorem coe_nonUnitalGelfandTransform_eq :
    ⇑(nonUnitalGelfandTransform ℂ A) =
      ⇑((puncturedGelfandStarTransform A).trans
        (ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ ℂ
          (CharacterSpace.homeoComplFstCharacter ℂ A).symm)) := by
  funext a
  exact (congrLeftStarAlgEquiv_puncturedGelfandStarTransform_apply A a).symm

/-- On a nonunital commutative C⋆-algebra `A`, `nonUnitalGelfandTransform ℂ A` is an isometry. -/
theorem nonUnitalGelfandTransform_isometry :
    Isometry (nonUnitalGelfandTransform ℂ A) := by
  rw [coe_nonUnitalGelfandTransform_eq A]
  exact StarAlgEquiv.isometry _

@[simp]
theorem norm_nonUnitalGelfandTransform (a : A) :
    ‖nonUnitalGelfandTransform ℂ A a‖ = ‖a‖ :=
  (nonUnitalGelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) a

/-- On a nonunital commutative C⋆-algebra `A`, `nonUnitalGelfandTransform ℂ A` is bijective. -/
theorem nonUnitalGelfandTransform_bijective :
    Function.Bijective (nonUnitalGelfandTransform ℂ A) := by
  rw [coe_nonUnitalGelfandTransform_eq A]
  exact EquivLike.bijective _

/-- **Nonunital Gelfand duality**: the nonunital Gelfand transform as an isometric `⋆`-algebra
equivalence between a nonunital commutative C⋆-algebra `A` and `C₀(characterSpace ℂ A, ℂ)`. -/
noncomputable def nonUnitalGelfandStarTransform : A ≃⋆ₐ[ℂ] C₀(characterSpace ℂ A, ℂ) :=
  StarAlgEquiv.ofBijective
    ({ nonUnitalGelfandTransform ℂ A with
      map_star' := nonUnitalGelfandTransform_map_star } : A →⋆ₙₐ[ℂ] C₀(characterSpace ℂ A, ℂ))
    (nonUnitalGelfandTransform_bijective A)

@[simp]
theorem coe_nonUnitalGelfandStarTransform :
    ⇑(nonUnitalGelfandStarTransform A) = nonUnitalGelfandTransform ℂ A := (rfl)

theorem nonUnitalGelfandStarTransform_apply (a : A) (φ : characterSpace ℂ A) :
    nonUnitalGelfandStarTransform A a φ = φ a := by
  simp [coe_nonUnitalGelfandStarTransform]

theorem norm_nonUnitalGelfandStarTransform (a : A) :
    ‖nonUnitalGelfandStarTransform A a‖ = ‖a‖ :=
  StarAlgEquiv.norm_map (nonUnitalGelfandStarTransform A) a

/-- `nonUnitalGelfandStarTransform A` factors as `puncturedGelfandStarTransform A` followed by
reindexing along `(CharacterSpace.homeoComplFstCharacter ℂ A).symm`. -/
theorem nonUnitalGelfandStarTransform_eq_punctured_trans_congrLeft :
    nonUnitalGelfandStarTransform A =
      (puncturedGelfandStarTransform A).trans
        (ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ ℂ
          (CharacterSpace.homeoComplFstCharacter ℂ A).symm) := by
  ext a φ
  simp

/-- Extending `f : C₀(characterSpace ℂ A, ℂ)` along `homeoComplFstCharacter ℂ A` and by `0` at
`fstCharacter ℂ A` recovers `((nonUnitalGelfandStarTransform A).symm f : Unitization ℂ A)` under the
unital Gelfand transform. -/
theorem inr_nonUnitalGelfandStarTransform_symm (f : C₀(characterSpace ℂ A, ℂ)) :
    ((nonUnitalGelfandStarTransform A).symm f : Unitization ℂ A) =
      (gelfandStarTransform (Unitization ℂ A)).symm
        ((ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ ℂ
          (CharacterSpace.homeoComplFstCharacter ℂ A) f).extendComplSingleton) := by
  rw [nonUnitalGelfandStarTransform_eq_punctured_trans_congrLeft]
  simp

/-- A nonunital commutative C⋆-algebra `A` admits a multiplicative identity if and only if its
character space `characterSpace ℂ A` is compact. -/
theorem compactSpace_characterSpace_iff_exists_mul_id :
    CompactSpace (characterSpace ℂ A) ↔ ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a := by
  constructor
  · intro hK
    let u : C₀(characterSpace ℂ A, ℂ) :=
      ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ (characterSpace ℂ A) ℂ 1
    refine ⟨(nonUnitalGelfandStarTransform A).symm u, fun a => ?_⟩
    have hea : (nonUnitalGelfandStarTransform A).symm u * a = a :=
      (EquivLike.injective (nonUnitalGelfandStarTransform A)) <| by
        rw [map_mul, (nonUnitalGelfandStarTransform A).apply_symm_apply]
        ext φ
        simp [u]
    exact ⟨hea, (mul_comm a _).trans hea⟩
  · rintro ⟨e, he⟩
    have hopen :=
      CharacterSpace.isOpen_singleton_fstCharacter_of_forall_mul_eq (𝕜 := ℂ) fun a => (he a).1
    have hcomp : CompactSpace
        ({CharacterSpace.fstCharacter ℂ A}ᶜ : Set (characterSpace ℂ (Unitization ℂ A))) :=
      (isOpen_singleton_iff_compactSpace_compl (CharacterSpace.fstCharacter ℂ A)).mp hopen
    exact (CharacterSpace.homeoComplFstCharacter ℂ A).symm.compactSpace

/-- In `characterSpace ℂ (Unitization ℂ A)`, the punctured space `{fstCharacter ℂ A}ᶜ` is compact
if and only if `A` admits a multiplicative identity. -/
theorem compactSpace_compl_fstCharacter_iff_exists_mul_id :
    CompactSpace
        ({CharacterSpace.fstCharacter ℂ A}ᶜ : Set (characterSpace ℂ (Unitization ℂ A))) ↔
      ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a := by
  rw [← compactSpace_characterSpace_iff_exists_mul_id A]
  exact ⟨fun _ => (CharacterSpace.homeoComplFstCharacter ℂ A).symm.compactSpace,
    fun _ => (CharacterSpace.homeoComplFstCharacter ℂ A).compactSpace⟩

/-- In `characterSpace ℂ (Unitization ℂ A)`, the scalar-projection character `fstCharacter ℂ A` is
isolated if and only if `A` admits a multiplicative identity. -/
theorem isOpen_singleton_fstCharacter_iff_exists_mul_id :
    IsOpen ({CharacterSpace.fstCharacter ℂ A} : Set (characterSpace ℂ (Unitization ℂ A))) ↔
      ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a :=
  (isOpen_singleton_iff_compactSpace_compl (CharacterSpace.fstCharacter ℂ A)).trans
    (compactSpace_compl_fstCharacter_iff_exists_mul_id A)

end NonUnitalCommCStarAlgebra

section UnitalComparison

variable (B : Type*) [CommCStarAlgebra B]

/-- For a unital commutative C⋆-algebra `B` viewed through its nonunital carrier,
`nonUnitalGelfandStarTransform B` agrees with `gelfandStarTransform B` composed with
`ContinuousMap.liftZeroAtInftyStarAlgEquiv`. -/
theorem nonUnitalGelfandStarTransform_eq_gelfandStarTransform_trans_liftZeroAtInfty :
    nonUnitalGelfandStarTransform B =
      (gelfandStarTransform B).trans
        (ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ (characterSpace ℂ B) ℂ) := by
  ext b φ
  simp

/-- For a unital commutative C⋆-algebra `B`, the punctured-unitization `⋆`-isomorphism
`puncturedGelfandStarTransform B` onto `C₀({fstCharacter ℂ B}ᶜ, ℂ)` recovers
`gelfandStarTransform B` after identifying `C₀({fstCharacter ℂ B}ᶜ, ℂ)` with
`C({fstCharacter ℂ B}ᶜ, ℂ)` and pulling back along `homeoComplFstCharacter ℂ B`. -/
theorem puncturedGelfandStarTransform_trans_eq_gelfandStarTransform :
    (puncturedGelfandStarTransform B).trans
      ((ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ
          ({CharacterSpace.fstCharacter ℂ B}ᶜ : Set (characterSpace ℂ (Unitization ℂ B)))
          ℂ).symm.trans
        ((CharacterSpace.homeoComplFstCharacter ℂ B).compStarAlgEquiv' ℂ ℂ)) =
      gelfandStarTransform B := by
  ext b φ
  simp

end UnitalComparison

end TauCeti
