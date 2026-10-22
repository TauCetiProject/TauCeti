/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hochschild.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The positive-arity suspended Hochschild complex

The degree-`p` cochains are the degree-`p` linear maps `Tᶜ(sA) → sA`. Since the source is a
direct sum over positive tensor lengths, a cochain includes an arbitrary family of Taylor
components, not merely a finitely supported family. The differential is the Gerstenhaber
commutator with the Taylor map of the A-infinity algebra. This file packages the existing
square-zero differential as a cochain complex of ground-ring modules and the Gerstenhaber
bracket as a bilinear map of the appropriate degree.

Degrees here are suspended degrees: an unsuspended arity-`n` map of internal degree `r` has
cochain degree `r + n - 1`. In particular the A-infinity structure has degree one. These are
positive-arity cochains, not the full Hochschild complex, which also has arity-zero cochains.
No characteristic-zero hypothesis is needed.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* M. Gerstenhaber, *The cohomology structure of an associative ring*.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.AInfinityAlgebra.PositiveHochschild

open ReducedTensorWords

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-- The submodule of positive-arity suspended Hochschild cochains of degree `p`. -/
def cochains (p : ℤ) : Submodule R (ReducedTensorWords R A →ₗ[R] A) :=
  LinearMap.homogeneousSubmodule (S := R) (gradedPiece (𝒜.grading.shift 1))
    (𝒜.grading.shift 1).piece p

@[simp]
theorem mem_cochains {p : ℤ} {F : ReducedTensorWords R A →ₗ[R] A} :
    F ∈ cochains 𝒜 p ↔ LinearMap.IsHomogeneous F (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece p := by
  rw [cochains, LinearMap.mem_homogeneousSubmodule]

/-- The differential on homogeneous cochains. The output degree is supplied by an equality,
so consumers can normalize degree arithmetic without transporting cochains. -/
def d (p q : ℤ) (h : p + 1 = q) : cochains 𝒜 p →ₗ[R] cochains 𝒜 q where
  toFun F := ⟨𝒜.hochschildDifferential p F, by
    simpa only [mem_cochains, ← h, add_comm 1 p] using
      𝒜.isHomogeneous_hochschildDifferential ((mem_cochains 𝒜).mp F.2)⟩
  map_add' F G := Subtype.ext (𝒜.hochschildDifferential_add p F G)
  map_smul' r F := Subtype.ext (𝒜.hochschildDifferential_smul p r F)

@[simp]
theorem coe_d (p q : ℤ) (h : p + 1 = q) (F : cochains 𝒜 p) :
    (d 𝒜 p q h F : ReducedTensorWords R A →ₗ[R] A) =
      𝒜.hochschildDifferential p F := (rfl)

/-- The homogeneous Hochschild differential squares to zero, with arbitrary output indices. -/
@[simp]
theorem d_d (p q r : ℤ) (hpq : p + 1 = q) (hqr : q + 1 = r) (F : cochains 𝒜 p) :
    d 𝒜 q r hqr (d 𝒜 p q hpq F) = 0 := by
  apply Subtype.ext
  simp only [coe_d, ZeroMemClass.coe_zero, ← hpq, add_comm p 1]
  exact 𝒜.hochschildDifferential_hochschildDifferential ((mem_cochains 𝒜).mp F.2)

/-- The positive-arity suspended Hochschild cochain complex, with differential `[m, -]`.
The abbreviation retains the degreewise cochain carriers. -/
abbrev complex : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R (cochains 𝒜 p))
    (fun p ↦ ModuleCat.ofHom (d 𝒜 p (p + 1) rfl)) (fun p ↦ by
      apply ModuleCat.hom_ext
      exact LinearMap.ext (d_d 𝒜 p (p + 1) (p + 1 + 1) rfl rfl))

/-- The adjacent complex differential is the homogeneous Hochschild differential. -/
@[simp]
theorem complex_d (p q : ℤ) (h : p + 1 = q) :
    (complex 𝒜).d p q = ModuleCat.ofHom (d 𝒜 p q h) := by
  subst q
  exact CochainComplex.of_d (fun p ↦ ModuleCat.of R (cochains 𝒜 p))
    (fun p ↦ ModuleCat.ofHom (d 𝒜 p (p + 1) rfl)) p

/-- The Gerstenhaber bracket of homogeneous cochains, bilinear and of summed degree.
As with `d`, the equality permits an arbitrary normalized output index. -/
def bracket {p q n : ℤ} (h : p + q = n) :
    cochains 𝒜 p →ₗ[R] cochains 𝒜 q →ₗ[R] cochains 𝒜 n :=
  LinearMap.mk₂ R
    (fun F G ↦ ⟨gerstenhaberBracket (𝒜.grading.shift 1) p q F G, by
      rw [mem_cochains, ← h]
      exact isHomogeneous_gerstenhaberBracket ((mem_cochains 𝒜).mp F.2)
        ((mem_cochains 𝒜).mp G.2)⟩)
    (fun _ _ _ ↦ Subtype.ext (gerstenhaberBracket_add_left ..))
    (fun _ _ _ ↦ Subtype.ext (gerstenhaberBracket_smul_left ..))
    (fun _ _ _ ↦ Subtype.ext (gerstenhaberBracket_add_right ..))
    (fun _ _ _ ↦ Subtype.ext (gerstenhaberBracket_smul_right ..))

@[simp]
theorem coe_bracket {p q n : ℤ} (h : p + q = n) (F : cochains 𝒜 p) (G : cochains 𝒜 q) :
    (bracket 𝒜 h F G : ReducedTensorWords R A →ₗ[R] A) =
      gerstenhaberBracket (𝒜.grading.shift 1) p q F G := by
  simp [bracket]

/-- Graded antisymmetry, with both brackets in the same normalized output degree. -/
theorem bracket_swap {p q n : ℤ} (h : p + q = n) (h' : q + p = n)
    (F : cochains 𝒜 p) (G : cochains 𝒜 q) :
    bracket 𝒜 h' G F = -negOnePowCast R (p * q) • bracket 𝒜 h F G := by
  apply Subtype.ext
  simp only [coe_bracket, SetLike.val_smul]
  exact gerstenhaberBracket_swap p q
    (F : ReducedTensorWords R A →ₗ[R] A) (G : ReducedTensorWords R A →ₗ[R] A)

/-- The graded Jacobi identity in Leibniz form, with a common output degree. -/
theorem leibniz_bracket {p q r n : ℤ} (h : p + q + r = n)
    (F : cochains 𝒜 p) (G : cochains 𝒜 q) (H : cochains 𝒜 r) :
    bracket 𝒜 (show p + (q + r) = n by omega) F (bracket 𝒜 rfl G H) =
      bracket 𝒜 h (bracket 𝒜 rfl F G) H +
        negOnePowCast R (p * q) •
          bracket 𝒜 (show q + (p + r) = n by omega) G (bracket 𝒜 rfl F H) := by
  apply Subtype.ext
  simp only [coe_bracket, Submodule.coe_add, Submodule.coe_smul]
  exact leibniz_gerstenhaberBracket ((mem_cochains 𝒜).mp F.2)
    ((mem_cochains 𝒜).mp G.2) ((mem_cochains 𝒜).mp H.2)

end TauCeti.AInfinityAlgebra.PositiveHochschild
