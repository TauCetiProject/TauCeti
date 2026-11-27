/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.ChangeOfFrame
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse

/-!
# Hermitian spaces with an adelic frame over a CM field

Let `E` be a CM field with complex conjugation `x ↦ conj x`, `E_∞ = ∏_w E_w` its infinite adeles and
`𝔸_f` its finite adeles, with the conjugation transported to both
(`NumberField.IsCMField.infiniteAdeleConj`, `NumberField.IsCMField.finiteAdeleConj`). On `E_∞` it
acts within each completion `E_w`, every infinite place of a CM field being its own conjugate. On
`𝔸_f` it carries the completion at a finite place `w` to the completion at the conjugate place
`conj w` (`IsDedekindDomain.FiniteAdeleRing.star_apply_conjPlace`), and these are two different
completions when `conj w ≠ w`, that is when the place of `E⁺` below `w` splits in `E`. An adelic
matrix is written by its archimedean and finite components, so `GL_n(𝔸)` is
`GL_n(E_∞) × GL_n(𝔸_f)` (Mathlib's `Matrix.GeneralLinearGroup.prodEquiv` identifies the two).
For a finite index set `ι` of size `n` and a sign vector `s ∈ {±1}^ι`, used at every infinite
place, `G(s) = G_∞(s) × G_f` is the adelic unitary group (`TauCeti.adelicUnitaryGroup`), where
`G_∞(s) = U(diag s)(E_∞)` and `G_f = U(1_n)(𝔸_f)`. This file defines:

* a **hermitian space with an adelic frame of signs `s`**, a pair `V = (J, x)` of a matrix
  `J ∈ M_n(E)` and `x ∈ GL_n(𝔸)` with `x* J x = diag(s)` at the infinite places and
  `x* J x = 1_n` at the finite places: the frame `x` pulls the form of `J` back to `diag(s)` and
  to `1_n`, sending the model coordinates to the space with Gram matrix `J`. Thus the hermitian
  form `h_J(u, v) = (conj u)ᵀ J v` on `E^n` has signature `(p, n - p)` at every infinite place and
  is isometric to the standard form `⟨1, …, 1⟩` at every finite place of `E⁺` (see below for the
  places of `E⁺` that split in `E`);
* its **rational points**: `γ ↦ x⁻¹ γ x` embeds `U(J)(E⁺) = {γ ∈ GL_n(E) : γ* J γ = J}` in
  `G(s)`, with image `Γ_V`, and `Γ_{V,f}` is the image of `Γ_V` in `G_f`;
* its **lattice** `Λ_V = {y ∈ E^n : (x⁻¹ y)_f ∈ Ô^n}`, an `𝓞_E`-submodule of `E^n`;
* the **moved space** `V · g = (J, x g)` for `g ∈ G(s)`, a right action of `G(s)` on the spaces
  of signs `s`, which conjugates the rational points;
* the **standard space** `I_n = (1_n, 1)`, of signs `(1, …, 1)`, whose lattice is `𝓞_E^n`.

The matrix `J` of a space is hermitian and invertible.

No CM type enters the definitions: at an infinite place `w` the conjugation of `E` extends to the
completion `E_w`, and read in `ℂ` through either embedding inducing `w` it is complex conjugation
(`NumberField.InfiniteAdeleRing.extensionEmbedding_star_apply`), so the condition
`x* J x = diag(s)` at `w` is the same for both identifications of `E_w` with `ℂ`.

At the finite places the frame equation `x* J x = 1_n` is not a condition on each component of `x`
separately: its component at a finite place `w` reads `σ(x_{conj w})ᵀ J x_w = 1_n`, where
`σ : E_{conj w} ≃ E_w` extends the conjugation of `E`. When `conj w = w`, that is when the place of
`E⁺` below `w` does not split in `E`, this says that `x_w` is an isometry from the standard form to
the form of `J` over `E_w`. When `conj w ≠ w`, that is when the place of `E⁺` below `w` splits in
`E`, the equation couples the two components `x_w` and `x_{conj w}`: it determines `x_{conj w}`
from `x_w`, the equation at `conj w` being equivalent to that at `w`.

## Main definitions

* `TauCeti.FramedHermitianSpace E s`: the hermitian spaces with an adelic frame of signs `s`.
* `TauCeti.FramedHermitianSpace.rationalEmbedding`, `rationalPoints`, `finiteRationalPoints`:
  the embedding `γ ↦ x⁻¹ γ x` and the groups `Γ_V` and `Γ_{V,f}`.
* `TauCeti.FramedHermitianSpace.lattice`: the lattice `Λ_V`.
* The right action `V · g` of `G(s)`, as a `MulAction` of `G(s)ᵐᵒᵖ`.
* `TauCeti.FramedHermitianSpace.standard E ι`: the standard space `I_n`.

## Main results

* `TauCeti.FramedHermitianSpace.mem_finiteRationalPoints_iff`: `Γ_{V,f}` consists of the
  `x_f⁻¹ γ x_f`, and `TauCeti.FramedHermitianSpace.finiteRationalPoints_eq_map`: it is the image of
  `Γ_V` in `G_f`.
* `TauCeti.FramedHermitianSpace.isHermitian_gram`, `TauCeti.FramedHermitianSpace.isUnit_gram`: the
  matrix `J` of a space is hermitian and invertible.
* `TauCeti.FramedHermitianSpace.rationalEmbedding_injective`: `γ ↦ x⁻¹ γ x` is injective.
* `TauCeti.FramedHermitianSpace.rationalPoints_smul`: `Γ_{V·g} = g⁻¹ Γ_V g`, and
  `TauCeti.FramedHermitianSpace.finiteRationalPoints_smul`: `Γ_{V·g, f} = g_f⁻¹ Γ_{V,f} g_f`.
* `TauCeti.FramedHermitianSpace.mem_lattice_standard_iff`: the lattice of `I_n` is `𝓞_E^n`.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §§2, 4.

## Attribution

The objects defined here follow `New.Space`, `New.Space.ratEmbed`, `New.Space.Γ`,
`New.Space.Γf`, `New.Space.baseLattice`, `New.stdSpace` and `New.Space.move`, and the statements on
the Gram matrix follow `New.Space.isUnit_J` and `New.Space.isHermitian_J`, in the files
`src/Lib/Adelic/Unitary/Defs.lean`, `src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean` and
`src/Lib/Adelic/Unitary/GramMatrix.lean` of grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC); the formalization here is independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-! ### Hermitian spaces with an adelic frame -/

/-- A **hermitian space with an adelic frame of signs `s`** over a CM field `E`: a matrix
`J ∈ M_n(E)`, the Gram matrix of the hermitian form `h_J(u, v) = (conj u)ᵀ J v` on `E^n`,
together with an adelic matrix `x ∈ GL_n(𝔸)`, given by its components in `GL_n(E_∞)` and
`GL_n(𝔸_f)`, such that `x* J x = diag(s)` at the infinite places and `x* J x = 1_n` at the finite
places. The matrix `J` is then hermitian and invertible (`isHermitian_gram`, `isUnit_gram`). -/
@[ext]
structure FramedHermitianSpace (s : ι → ℤˣ) where
  /-- The Gram matrix `J` of the hermitian form. -/
  gram : Matrix ι ι E
  /-- The adelic frame `x`, by its archimedean and finite components. -/
  frame : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]
  /-- At the infinite places the frame pulls the form of `J` back to that of `diag(s)`: it sends
  the model coordinates into the space with Gram matrix `J`, preserving the forms. -/
  star_mul_gram_mul_fst : star (frame.1 : Matrix ι ι (InfiniteAdeleRing E)) *
      gram.map (algebraMap E (InfiniteAdeleRing E)) * frame.1 =
    diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)
  /-- At the finite places the frame pulls the form of `J` back to the standard form `1_n`: it
  sends the model coordinates into the space with Gram matrix `J`, preserving the forms. -/
  star_mul_gram_mul_snd :
    star (frame.2 : Matrix ι ι 𝔸ᶠ[E]) * gram.map (algebraMap E 𝔸ᶠ[E]) * frame.2 = 1

namespace FramedHermitianSpace

variable {E} {s : ι → ℤˣ} (V : FramedHermitianSpace E s)

/-- **The Gram matrix of a space with an adelic frame is hermitian**: by the finite frame equation
`x* J x = 1_n`, its image over the finite adeles is self-adjoint. -/
theorem isHermitian_gram : V.gram.IsHermitian := by
  have h : IsSelfAdjoint
      (star (V.frame.2 : Matrix ι ι 𝔸ᶠ[E]) * V.gram.map (algebraMap E 𝔸ᶠ[E]) * V.frame.2) := by
    rw [V.star_mul_gram_mul_snd]
    exact .one _
  exact (isHermitian_map_iff (fun x ↦ algebraMap_star_comm x)
    (FiniteAdeleRing.algebraMap_injective E (RingOfIntegers.not_isField E))).1
    (V.frame.2.isUnit.isSelfAdjoint_conjugate_iff'.1 h)

/-- **The Gram matrix of a space with an adelic frame is invertible**: the frame pulls its image
over the finite adeles back to `1_n`. -/
theorem isUnit_gram : IsUnit V.gram := by
  have h : IsUnit
      (star (V.frame.2 : Matrix ι ι 𝔸ᶠ[E]) * V.gram.map (algebraMap E 𝔸ᶠ[E]) * V.frame.2) := by
    rw [V.star_mul_gram_mul_snd]
    exact isUnit_one
  -- `𝔸_f` is nontrivial, so `algebraMap E 𝔸_f` is a local homomorphism.
  have := (FiniteAdeleRing.algebraMap_injective E (RingOfIntegers.not_isField E)).nontrivial
  exact (Matrix.isUnit_map_iff (algebraMap E 𝔸ᶠ[E]) V.gram).1
    (IsUnit.mul_iff.1 (IsUnit.mul_iff.1 h).1).2

/-! ### Rational points -/

/-- The **rational embedding** `γ ↦ x⁻¹ γ x` of the group `U(J)(E⁺) = {γ ∈ GL_n(E) : γ* J γ = J}`
of rational points of the unitary group of the Gram matrix in the adelic unitary group `G(s)`,
`γ` being read diagonally in `GL_n(𝔸)`: the pair of the conjugations by the two components of the
frame, which carry `U(J)` into `G_∞(s)` and into `G_f` as the frame pulls `J` back to `diag(s)`
and to `1_n`. -/
def rationalEmbedding : unitaryGroupOf V.gram →* adelicUnitaryGroup E s :=
  let infinite := (unitaryGroupOf.conjEquiv V.frame.1 V.star_mul_gram_mul_fst).toMonoidHom.comp
    (unitaryGroupOf.mapHom V.gram (algebraMap E (InfiniteAdeleRing E))
      (fun x ↦ algebraMap_star_comm x))
  let finite := (unitaryGroupOf.conjEquiv V.frame.2 V.star_mul_gram_mul_snd).toMonoidHom.comp
    (unitaryGroupOf.mapHom V.gram (algebraMap E 𝔸ᶠ[E]) (fun x ↦ algebraMap_star_comm x))
  (((unitaryGroupOf _).subtype.comp infinite).prod
    ((unitaryGroupOf _).subtype.comp finite)).codRestrict _ fun γ ↦
      ⟨(infinite γ).property, unitaryGroupOf_one.le (finite γ).property⟩

/-- The rational embedding is `γ ↦ x⁻¹ γ x`. -/
@[simp]
theorem coe_rationalEmbedding (γ : unitaryGroupOf V.gram) :
    (V.rationalEmbedding γ : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) =
      (V.frame.1⁻¹ * GeneralLinearGroup.map (algebraMap E (InfiniteAdeleRing E)) γ * V.frame.1,
        V.frame.2⁻¹ * GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ * V.frame.2) := by
  simp [rationalEmbedding, MonoidHom.codRestrict]

/-- The rational embedding is injective. -/
theorem rationalEmbedding_injective : Function.Injective V.rationalEmbedding := by
  intro γ δ h
  apply (unitaryGroupOf.conjEquiv V.frame.2 V.star_mul_gram_mul_snd).injective.comp
    (unitaryGroupOf.mapHom_injective (fun x ↦ algebraMap_star_comm x)
      (FiniteAdeleRing.algebraMap_injective E (RingOfIntegers.not_isField E)))
  apply Subtype.ext
  simpa only [Function.comp_apply, unitaryGroupOf.coe_conjEquiv_apply, unitaryGroupOf.coe_mapHom,
    coe_rationalEmbedding] using
    congrArg (fun g : adelicUnitaryGroup E s ↦ (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2) h

/-- The **rational points** `Γ_V` of a space with an adelic frame: the image of `U(J)(E⁺)` in the
adelic unitary group `G(s)` under the rational embedding `γ ↦ x⁻¹ γ x`. -/
def rationalPoints : Subgroup (adelicUnitaryGroup E s) :=
  V.rationalEmbedding.range

/-- The rational points `Γ_V` are the range of the rational embedding; with
`MonoidHom.mem_range`, this describes membership in `Γ_V`. -/
theorem rationalPoints_def : V.rationalPoints = V.rationalEmbedding.range :=
  (rfl)

/-- The **finite rational points** `Γ_{V,f}` of a space with an adelic frame: the image in the
finite adelic unitary group `G_f` of `U(J)(E⁺)` under the rational embedding followed by the
finite component, that is the image of the rational points `Γ_V` in `G_f`
(`finiteRationalPoints_eq_map`). -/
def finiteRationalPoints : Subgroup (finiteAdelicUnitaryGroup E ι) :=
  ((adelicUnitaryGroup.finitePart E s).comp V.rationalEmbedding).range

/-- The finite rational points `Γ_{V,f}` are the range of the rational embedding followed by the
finite component. -/
theorem finiteRationalPoints_def :
    V.finiteRationalPoints = ((adelicUnitaryGroup.finitePart E s).comp V.rationalEmbedding).range :=
  (rfl)

/-- `Γ_{V,f}` is the image of the rational points `Γ_V` in `G_f`. -/
theorem finiteRationalPoints_eq_map :
    V.finiteRationalPoints = V.rationalPoints.map (adelicUnitaryGroup.finitePart E s) := by
  rw [finiteRationalPoints_def, rationalPoints_def, MonoidHom.range_comp]

/-- `Γ_{V,f}` consists of the conjugates `x_f⁻¹ γ x_f` of the elements `γ ∈ U(J)(E⁺)` by the
finite component `x_f` of the frame. -/
theorem mem_finiteRationalPoints_iff {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ V.finiteRationalPoints ↔ ∃ γ : unitaryGroupOf V.gram,
      V.frame.2⁻¹ * GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ * V.frame.2 =
        (g : GL ι 𝔸ᶠ[E]) := by
  simp only [finiteRationalPoints_def, MonoidHom.mem_range, MonoidHom.comp_apply, Subtype.ext_iff,
    adelicUnitaryGroup.coe_finitePart, coe_rationalEmbedding]

/-! ### The lattice -/

/-- The **lattice** `Λ_V = {y ∈ E^n : (x⁻¹ y)_f ∈ Ô^n}` of a space with an adelic frame: the vectors
of `E^n`, read diagonally in `𝔸_f^n`, that the inverse of the finite component of the frame
carries to integral vectors. It is the preimage of the `𝓞_E`-submodule `Ô^n` of `𝔸_f^n` under the
`𝓞_E`-linear map `y ↦ x_f⁻¹ y`, so an `𝓞_E`-submodule of `E^n`. -/
def lattice : Submodule (𝓞 E) (ι → E) :=
  (Submodule.pi Set.univ fun _ : ι ↦ (FiniteAdeleRing.integralAdeles (𝓞 E) E).toSubmodule).comap
    ((mulVecLin (↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E])).restrictScalars (𝓞 E) ∘ₗ
      ((Algebra.linearMap E 𝔸ᶠ[E]).compLeft ι).restrictScalars (𝓞 E))

/-- `y ∈ Λ_V` exactly when `(x⁻¹ y)_f` is integral. -/
theorem mem_lattice_iff {y : ι → E} :
    y ∈ V.lattice ↔ ∀ i, ((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ y)) i ∈
      FiniteAdeleRing.integralAdeles (𝓞 E) E := by
  rw [lattice, Submodule.mem_comap]
  refine Submodule.mem_pi.trans (forall_congr' fun i ↦ ?_)
  simp only [Set.mem_univ, true_implies, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  -- What remains is `(Algebra.linearMap E 𝔸_f).compLeft ι y = algebraMap E 𝔸_f ∘ y` and
  -- `Subalgebra.mem_toSubmodule`, true by definition. Neither `rw` nor `simp` applies them: `Ô` is
  -- a submodule for the `𝓞 E`-module structure `FiniteAdeleRing.instAlgebra_1` of `𝔸_f`, while
  -- instance synthesis gives the linear map the structure `RingOfIntegers.instAlgebra E` through
  -- `E`, which agrees with it only up to unfolding.
  exact Iff.rfl

/-! ### The moved space -/

/-- The right action of the adelic unitary group `G(s)` on the spaces with an adelic frame of
signs `s`: the **moved space** `V · g = (J, x g)`. -/
instance : MulAction (adelicUnitaryGroup E s)ᵐᵒᵖ (FramedHermitianSpace E s) where
  smul g V :=
    { gram := V.gram
      frame := V.frame * g.unop
      -- `x g` pulls `J` back to the forms of `x`, as `g` preserves them.
      star_mul_gram_mul_fst := by
        rw [Prod.fst_mul, Units.val_mul]
        exact star_mul_mul_mul_eq_of_mem_unitaryGroupOf V.star_mul_gram_mul_fst g.unop.property.1
      star_mul_gram_mul_snd := by
        rw [Prod.snd_mul, Units.val_mul]
        exact star_mul_mul_mul_eq_of_mem_unitaryGroupOf V.star_mul_gram_mul_snd
          (unitaryGroupOf_one.ge g.unop.property.2) }
  -- Elaborated as tactic blocks, after the proofs in `smul`, so that the frames reduce.
  one_smul V := by exact FramedHermitianSpace.ext rfl (mul_one V.frame)
  mul_smul _ _ _ := by exact FramedHermitianSpace.ext rfl (mul_assoc _ _ _).symm

/-- Moving a space does not change its Gram matrix. -/
@[simp]
theorem gram_smul (g : (adelicUnitaryGroup E s)ᵐᵒᵖ) : (g • V).gram = V.gram :=
  (rfl)

/-- The frame of the moved space `V · g` is `x g`. -/
@[simp]
theorem frame_smul (g : (adelicUnitaryGroup E s)ᵐᵒᵖ) :
    (g • V).frame = V.frame * (g.unop : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) :=
  (rfl)

/-- The rational embedding of the moved space `V · g` is that of `V` followed by conjugation by
`g⁻¹`: `(x g)⁻¹ γ (x g) = g⁻¹ (x⁻¹ γ x) g`. -/
theorem rationalEmbedding_smul (g : (adelicUnitaryGroup E s)ᵐᵒᵖ) (γ : unitaryGroupOf V.gram) :
    (g • V).rationalEmbedding γ = MulAut.conj g.unop⁻¹ (V.rationalEmbedding γ) := by
  refine Subtype.ext (Prod.ext ?_ ?_) <;>
  simp only [coe_rationalEmbedding, frame_smul, MulAut.conj_apply, inv_inv, Subgroup.coe_mul,
    Subgroup.coe_inv, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, _root_.mul_inv_rev,
    mul_assoc]

/-- **Rational points of a moved space**: `Γ_{V·g} = g⁻¹ Γ_V g`. -/
theorem rationalPoints_smul (g : (adelicUnitaryGroup E s)ᵐᵒᵖ) :
    (g • V).rationalPoints = V.rationalPoints.map (MulAut.conj g.unop⁻¹).toMonoidHom := by
  rw [rationalPoints_def, rationalPoints_def, MonoidHom.map_range]
  exact congrArg MonoidHom.range (MonoidHom.ext (V.rationalEmbedding_smul g))

/-- **Finite rational points of a moved space**: `Γ_{V·g, f} = g_f⁻¹ Γ_{V,f} g_f`, for `g_f` the
finite component of `g`. -/
theorem finiteRationalPoints_smul (g : (adelicUnitaryGroup E s)ᵐᵒᵖ) :
    (g • V).finiteRationalPoints = V.finiteRationalPoints.map
      (MulAut.conj (adelicUnitaryGroup.finitePart E s g.unop)⁻¹).toMonoidHom := by
  rw [finiteRationalPoints_eq_map, finiteRationalPoints_eq_map, rationalPoints_smul,
    Subgroup.map_map, Subgroup.map_map]
  -- the finite component of `g⁻¹ h g` is `g_f⁻¹ h_f g_f`
  exact congrArg V.rationalPoints.map (MonoidHom.ext fun h ↦ by simp)

/-- Moving a space by an element of `G(s)` whose finite component lies in
`K₀ = G_f ∩ GL_n(Ô)` does not change its lattice. -/
theorem lattice_smul_of_mem_integralAdelicUnitaryGroup (g : (adelicUnitaryGroup E s)ᵐᵒᵖ)
    (hg : adelicUnitaryGroup.finitePart E s g.unop ∈ integralAdelicUnitaryGroup E ι) :
    (g • V).lattice = V.lattice := by
  -- `(x g)_f⁻¹ y = g_f⁻¹ (x_f⁻¹ y)`, and `g_f⁻¹ ∈ GL_n(Ô)` preserves the integral vectors.
  have hg' : (g.unop : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2⁻¹ ∈
      (FiniteAdeleRing.integralGL E ι).range := by
    simpa only [InvMemClass.coe_inv, adelicUnitaryGroup.coe_finitePart] using
      mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL.1 (inv_mem hg)
  ext y
  rw [mem_lattice_iff, mem_lattice_iff, frame_smul, Prod.snd_mul, _root_.mul_inv_rev,
    Units.val_mul, ← mulVec_mulVec]
  exact FiniteAdeleRing.forall_mulVec_mem_integralAdeles_iff hg'

/-! ### The standard space -/

variable (E ι) in
/-- The **standard space** `I_n = (1_n, 1)`: the standard hermitian form `⟨1, …, 1⟩` on `E^n`
with the trivial adelic frame, of signs `(1, …, 1)`. -/
def standard : FramedHermitianSpace E (1 : ι → ℤˣ) where
  gram := 1
  frame := 1
  star_mul_gram_mul_fst := by simp
  star_mul_gram_mul_snd := by simp

/-- The Gram matrix of the standard space is `1_n`. -/
@[simp]
theorem gram_standard : (standard E ι).gram = 1 :=
  (rfl)

/-- The frame of the standard space is `1`. -/
@[simp]
theorem frame_standard : (standard E ι).frame = 1 :=
  (rfl)

/-- **The lattice of the standard space is `𝓞_E^n`.** -/
theorem mem_lattice_standard_iff {y : ι → E} :
    y ∈ (standard E ι).lattice ↔ ∀ i, y i ∈ (algebraMap (𝓞 E) E).range := by
  simp [mem_lattice_iff, FiniteAdeleRing.algebraMap_mem_integralAdeles_iff]

end FramedHermitianSpace

end TauCeti
