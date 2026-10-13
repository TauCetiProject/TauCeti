/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMulAction
public import TauCeti.Algebra.Module.GradedModule.Internal
import TauCeti.Algebra.DirectSum.Internal

/-!
# Homogeneous parts of linear maps

The degree-`r` part of a map sends a homogeneous input of degree `p` to the
degree-`(p + r)` projection of its image. Summing over the finite homogeneous decomposition
of the input defines this operation even when the map is not a finite sum of homogeneous maps.

`InternalGrading.homogeneousPart` is linear over the coefficient semiring of the grading.
`InternalGrading.homogeneousPartOfGradedSMul` instead preserves linearity over a graded scalar
semiring acting compatibly on both modules. Its action need not be related to the coefficient
action by a scalar tower.

The construction is shared by homogeneous splittings, polynomial-linear retractions, and the
degree-zero lift that makes projective underlying modules projective in the graded category.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projective modules and the homogeneous-component argument.
-/

public section

noncomputable section

namespace TauCeti.InternalGrading

universe uk uA uM uN uP

variable {k : Type uk} [Semiring k]
  {M : Type uM} [AddCommMonoid M] [Module k M]
  {N : Type uN} [AddCommMonoid N] [Module k N]
  (G : InternalGrading k M) (H : InternalGrading k N)

-- Assemble additively so the scalar action on a map need not agree with the coefficient action.
private def homogeneousPartAddHom (f : M →+ N) (r : ℤ) : M →+ N :=
  (DirectSum.toAddMonoid fun p ↦
    (AddSubmonoidClass.subtype (H.piece (p + r))).comp <|
      (DFinsupp.evalAddMonoidHom (p + r)).comp <|
        (DirectSum.decomposeAddEquiv H.piece).toAddMonoidHom.comp <|
          f.comp (AddSubmonoidClass.subtype (G.piece p))).comp
    (DirectSum.decomposeAddEquiv G.piece).toAddMonoidHom

private theorem homogeneousPartAddHom_apply_of_mem (f : M →+ N) (r : ℤ)
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) :
    homogeneousPartAddHom G H f r x = (DirectSum.decompose H.piece (f x) (p + r) : N) := by
  simp [homogeneousPartAddHom, DirectSum.decompose_of_mem G.piece hx, DFinsupp.evalAddMonoidHom]

private theorem homogeneousPartAddHom_map_smul {A : Type uA}
    [DistribSMul A M] [DistribSMul A N] (f : M →+ N) (r s : ℤ) (a : A)
    (hf : ∀ x, f (a • x) = a • f x)
    (hG : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → a • x ∈ G.piece (p + s))
    (hH : ∀ ⦃p : ℤ⦄ ⦃y : N⦄, y ∈ H.piece p → a • y ∈ H.piece (p + s)) (x : M) :
    homogeneousPartAddHom G H f r (a • x) = a • homogeneousPartAddHom G H f r x := by
  induction x using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | @homogeneous p x =>
    rw [homogeneousPartAddHom_apply_of_mem G H f r (hG x.2), hf,
      homogeneousPartAddHom_apply_of_mem G H f r x.2]
    have hindex : (p + s) + r = (p + r) + s := by omega
    rw [hindex]
    exact (DirectSum.map_decompose_shift H.piece H.piece (DistribSMul.toAddMonoidHom N a)
      (· + s) (add_left_injective s) (fun _ _ hy ↦ hH hy) (p + r) (f x)).symm
  | add x y hx hy => simp [smul_add, hx, hy]

/-- The degree-`r` part of a coefficient-linear map. On each degree-`p` input component it
retains the degree-`(p + r)` component of the image. -/
def homogeneousPart (f : M →ₗ[k] N) (r : ℤ) : M →ₗ[k] N where
  toFun := homogeneousPartAddHom G H f.toAddMonoidHom r
  map_add' := map_add _
  map_smul' a x := homogeneousPartAddHom_map_smul G H f.toAddMonoidHom r 0 a
    (f.map_smul a) (fun _ _ hx ↦ by simpa using (G.piece _).smul_mem a hx)
    (fun _ _ hy ↦ by simpa using (H.piece _).smul_mem a hy) x

/-- The value of a homogeneous part on a homogeneous input. -/
theorem homogeneousPart_apply_of_mem (f : M →ₗ[k] N) (r : ℤ)
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) :
    G.homogeneousPart H f r x = (DirectSum.decompose H.piece (f x) (p + r) : N) :=
  homogeneousPartAddHom_apply_of_mem G H f.toAddMonoidHom r hx

/-- A homogeneous part commutes with any scalar whose action shifts both gradings by the same
degree and commutes with the original map. -/
theorem homogeneousPart_apply_smul {A : Type uA} [DistribSMul A M] [DistribSMul A N]
    (f : M →ₗ[k] N) (r s : ℤ) (a : A) (hf : ∀ x, f (a • x) = a • f x)
    (hG : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → a • x ∈ G.piece (p + s))
    (hH : ∀ ⦃p : ℤ⦄ ⦃y : N⦄, y ∈ H.piece p → a • y ∈ H.piece (p + s)) (x : M) :
    G.homogeneousPart H f r (a • x) = a • G.homogeneousPart H f r x :=
  homogeneousPartAddHom_map_smul G H f.toAddMonoidHom r s a hf hG hH x

/-- The degree-`r` part is homogeneous of degree `r`. -/
@[simp]
theorem isHomogeneous_homogeneousPart (f : M →ₗ[k] N) (r : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (G.homogeneousPart H f r) G.piece H.piece r := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  rw [G.homogeneousPart_apply_of_mem H f r hx]
  exact (DirectSum.decompose H.piece (f x) (p + r)).property

/-- Taking the component at the degree of a homogeneous map recovers the map. -/
@[simp]
theorem homogeneousPart_eq_self (f : M →ₗ[k] N) (r : ℤ)
    (hf : TauCeti.LinearMap.IsHomogeneous f G.piece H.piece r) :
    G.homogeneousPart H f r = f := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  rw [G.homogeneousPart_apply_of_mem H f r hx]
  exact DirectSum.decompose_of_mem_same H.piece (hf.map_mem hx)

/-- A map is fixed by its degree-`r` component exactly when it is homogeneous of degree `r`. -/
@[simp]
theorem homogeneousPart_eq_self_iff (f : M →ₗ[k] N) (r : ℤ) :
    G.homogeneousPart H f r = f ↔ TauCeti.LinearMap.IsHomogeneous f G.piece H.piece r := by
  constructor
  · intro hf
    rw [← hf]
    exact G.isHomogeneous_homogeneousPart H f r
  · exact G.homogeneousPart_eq_self H f r

/-- Taking a homogeneous part preserves addition of maps. -/
@[simp]
theorem homogeneousPart_add (f g : M →ₗ[k] N) (r : ℤ) :
    G.homogeneousPart H (f + g) r = G.homogeneousPart H f r + G.homogeneousPart H g r := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  simp [G.homogeneousPart_apply_of_mem H (f + g) r hx,
    G.homogeneousPart_apply_of_mem H f r hx, G.homogeneousPart_apply_of_mem H g r hx]

section Composition

variable {P : Type uP} [AddCommMonoid P] [Module k P] (I : InternalGrading k P)

-- Work with the shared additive construction: a graded-scalar map need not be coefficient-linear.
private theorem comp_homogeneousPartAddHom_apply_of_mem {A : Type uA} [Semiring A]
    [Module A N] [Module A P] (f : M →+ N) (r : ℤ) {g : N →ₗ[A] P} {s : ℤ}
    (hg : TauCeti.LinearMap.IsHomogeneous g H.piece I.piece s)
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) :
    g (homogeneousPartAddHom G H f r x) =
      homogeneousPartAddHom G I (g.toAddMonoidHom.comp f) (r + s) x := by
  rw [homogeneousPartAddHom_apply_of_mem G H f r hx,
    homogeneousPartAddHom_apply_of_mem G I (g.toAddMonoidHom.comp f) (r + s) hx,
    hg.map_decompose, add_assoc]
  rfl

private theorem homogeneousPartAddHom_comp_apply_of_mem {A : Type uA} [Semiring A]
    [Module A M] [Module A N] (f : N →+ P) (r : ℤ) {g : M →ₗ[A] N} {s : ℤ}
    (hg : TauCeti.LinearMap.IsHomogeneous g G.piece H.piece s)
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) :
    homogeneousPartAddHom G I (f.comp g.toAddMonoidHom) (s + r) x =
      homogeneousPartAddHom H I f r (g x) := by
  rw [homogeneousPartAddHom_apply_of_mem G I (f.comp g.toAddMonoidHom) (s + r) hx,
    homogeneousPartAddHom_apply_of_mem H I f r (hg.map_mem hx), add_assoc]
  rfl

/-- Postcomposition by a degree-`s` homogeneous coefficient-linear map shifts the selected
component by `s`. -/
theorem comp_homogeneousPart (f : M →ₗ[k] N) (r : ℤ) {g : N →ₗ[k] P} {s : ℤ}
    (hg : TauCeti.LinearMap.IsHomogeneous g H.piece I.piece s) :
    g.comp (G.homogeneousPart H f r) = G.homogeneousPart I (g.comp f) (r + s) := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  exact comp_homogeneousPartAddHom_apply_of_mem G H I f.toAddMonoidHom r hg hx

/-- Precomposition by a degree-`s` homogeneous coefficient-linear map shifts the selected
component by `s`. -/
theorem homogeneousPart_comp (f : N →ₗ[k] P) (r : ℤ) {g : M →ₗ[k] N} {s : ℤ}
    (hg : TauCeti.LinearMap.IsHomogeneous g G.piece H.piece s) :
    G.homogeneousPart I (f.comp g) (s + r) = (H.homogeneousPart I f r).comp g := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  exact homogeneousPartAddHom_comp_apply_of_mem G H I f.toAddMonoidHom r hg hx

end Composition

section GradedSMul

variable {A : Type uA} [Semiring A] [Module A M] [Module A N]
  {S : Type*} [SetLike S A] [AddSubmonoidClass S A] (𝒜 : ℤ → S)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedSMul 𝒜 G.piece] [SetLike.GradedSMul 𝒜 H.piece]

include 𝒜 in
private theorem homogeneousPartAddHom_map_smul_of_graded (f : M →ₗ[A] N) (r : ℤ)
    (a : A) (x : M) :
    homogeneousPartAddHom G H f.toAddMonoidHom r (a • x) =
      a • homogeneousPartAddHom G H f.toAddMonoidHom r x := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    exact homogeneousPartAddHom_map_smul G H f.toAddMonoidHom r i (a : A)
      (f.map_smul a) (fun _ _ hx ↦ by simpa [add_comm] using SetLike.GradedSMul.smul_mem a.2 hx)
      (fun _ _ hy ↦ by simpa [add_comm] using SetLike.GradedSMul.smul_mem a.2 hy) x
  | add a b ha hb => simp [add_smul, ha, hb]

/-- The degree-`r` part of an `A`-linear map for a common graded scalar action. The coefficient
and scalar semirings may act independently, and the scalar pieces may be any additive subobjects.
-/
def homogeneousPartOfGradedSMul (f : M →ₗ[A] N) (r : ℤ) : M →ₗ[A] N where
  toFun := homogeneousPartAddHom G H f.toAddMonoidHom r
  map_add' := map_add _
  map_smul' := homogeneousPartAddHom_map_smul_of_graded G H 𝒜 f r

/-- On a homogeneous input, the graded-scalar homogeneous part selects the output component. -/
theorem homogeneousPartOfGradedSMul_apply_of_mem (f : M →ₗ[A] N) (r : ℤ)
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) :
    G.homogeneousPartOfGradedSMul H 𝒜 f r x =
      (DirectSum.decompose H.piece (f x) (p + r) : N) :=
  homogeneousPartAddHom_apply_of_mem G H f.toAddMonoidHom r hx

/-- The graded-scalar homogeneous part has the selected degree. -/
@[simp]
theorem isHomogeneous_homogeneousPartOfGradedSMul (f : M →ₗ[A] N) (r : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (G.homogeneousPartOfGradedSMul H 𝒜 f r)
      G.piece H.piece r := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  rw [G.homogeneousPartOfGradedSMul_apply_of_mem H 𝒜 f r hx]
  exact (DirectSum.decompose H.piece (f x) (p + r)).property

/-- Taking the component at the degree of a homogeneous graded-scalar map recovers the map. -/
@[simp]
theorem homogeneousPartOfGradedSMul_eq_self (f : M →ₗ[A] N) (r : ℤ)
    (hf : TauCeti.LinearMap.IsHomogeneous f G.piece H.piece r) :
    G.homogeneousPartOfGradedSMul H 𝒜 f r = f := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  rw [G.homogeneousPartOfGradedSMul_apply_of_mem H 𝒜 f r hx]
  exact DirectSum.decompose_of_mem_same H.piece (hf.map_mem hx)

/-- A graded-scalar map is fixed by its degree-`r` component exactly when it has degree `r`. -/
@[simp]
theorem homogeneousPartOfGradedSMul_eq_self_iff (f : M →ₗ[A] N) (r : ℤ) :
    G.homogeneousPartOfGradedSMul H 𝒜 f r = f ↔
      TauCeti.LinearMap.IsHomogeneous f G.piece H.piece r := by
  constructor
  · intro hf
    rw [← hf]
    exact G.isHomogeneous_homogeneousPartOfGradedSMul H 𝒜 f r
  · exact G.homogeneousPartOfGradedSMul_eq_self H 𝒜 f r

/-- Taking a graded-scalar homogeneous part preserves addition. -/
@[simp]
theorem homogeneousPartOfGradedSMul_add (f g : M →ₗ[A] N) (r : ℤ) :
    G.homogeneousPartOfGradedSMul H 𝒜 (f + g) r =
      G.homogeneousPartOfGradedSMul H 𝒜 f r + G.homogeneousPartOfGradedSMul H 𝒜 g r := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  simp [G.homogeneousPartOfGradedSMul_apply_of_mem H 𝒜 (f + g) r hx,
    G.homogeneousPartOfGradedSMul_apply_of_mem H 𝒜 f r hx,
    G.homogeneousPartOfGradedSMul_apply_of_mem H 𝒜 g r hx]

variable {P : Type uP} [AddCommMonoid P] [Module k P] [Module A P]
  (I : InternalGrading k P) [SetLike.GradedSMul 𝒜 I.piece]

/-- Postcomposition by a degree-`s` homogeneous map shifts the selected component by `s`. -/
theorem comp_homogeneousPartOfGradedSMul (f : M →ₗ[A] N) (r : ℤ) {g : N →ₗ[A] P} {s : ℤ}
    (hg : TauCeti.LinearMap.IsHomogeneous g H.piece I.piece s) :
    g.comp (G.homogeneousPartOfGradedSMul H 𝒜 f r) =
      G.homogeneousPartOfGradedSMul I 𝒜 (g.comp f) (r + s) := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  exact comp_homogeneousPartAddHom_apply_of_mem G H I f.toAddMonoidHom r hg hx

/-- Precomposition by a degree-`s` homogeneous map shifts the selected component by `s`. -/
theorem homogeneousPartOfGradedSMul_comp (f : N →ₗ[A] P) (r : ℤ) {g : M →ₗ[A] N} {s : ℤ}
    (hg : TauCeti.LinearMap.IsHomogeneous g G.piece H.piece s) :
    G.homogeneousPartOfGradedSMul I 𝒜 (f.comp g) (s + r) =
      (H.homogeneousPartOfGradedSMul I 𝒜 f r).comp g := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  exact homogeneousPartAddHom_comp_apply_of_mem G H I f.toAddMonoidHom r hg hx

end GradedSMul

end TauCeti.InternalGrading
