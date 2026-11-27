/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse

/-!
# Hermitian spaces with an adelic frame over a CM field

Let `E` be a CM field with complex conjugation `x ↦ conj x`, `E_∞ = ∏_w E_w` its infinite adeles and
`𝔸_f` its finite adeles, with the conjugation transported to both
(`NumberField.IsCMField.infiniteAdeleConj`, `NumberField.IsCMField.finiteAdeleConj`). On `E_∞` it
acts within each completion `E_w`, every infinite place of a CM field being its own conjugate. On
`𝔸_f` it carries the completion at a finite place `w` to the completion at the conjugate place
`conj w` (`NumberField.IsCMField.finiteAdeleRing_star_apply`), and these are two different
completions when `w` splits in `E / E⁺`. An adelic matrix is written by its archimedean and finite
components, so `GL_n(𝔸)` is `GL_n(E_∞) × GL_n(𝔸_f)` (Mathlib's
`Matrix.GeneralLinearGroup.prodEquiv` identifies the two).
For a finite index set `ι` of size `n` and a sign vector `s ∈ {±1}^ι`, used at every infinite
place, this file defines:

* the **adelic unitary group** `G(s) = G_∞(s) × G_f`, where `G_∞(s) = U(diag s)(E_∞)` is the
  product over the infinite places of the unitary groups of `diag(s)`, each `≅ U(p, n - p)` for
  `p` the number of signs `+1`, and `G_f = U(1_n)(𝔸_f)` is the finite adelic unitary group
  (`TauCeti.finiteAdelicUnitaryGroup`);
* a **hermitian space with an adelic frame of signs `s`**, a pair `V = (J, x)` of a matrix
  `J ∈ M_n(E)` and `x ∈ GL_n(𝔸)` with `x* J x = diag(s)` at the infinite places and
  `x* J x = 1_n` at the finite places. Thus the hermitian form `h_J(u, v) = (conj u)ᵀ J v` on
  `E^n` has signature `(p, n - p)` at every infinite place and is isometric to the standard form
  `⟨1, …, 1⟩` at every finite place of `E⁺` (see below for the split places);
* its **rational points**: `γ ↦ x⁻¹ γ x` embeds `U(J)(E⁺) = {γ ∈ GL_n(E) : γ* J γ = J}` in
  `G(s)`, with image `Γ_V`, and `Γ_{V,f}` is the image of `Γ_V` in `G_f`;
* its **lattice** `Λ_V = {y ∈ E^n : (x⁻¹ y)_f ∈ Ô^n}`, an `𝓞_E`-submodule of `E^n`;
* the **moved space** `V · g = (J, x g)` for `g ∈ G(s)`, a right action of `G(s)` on the spaces
  of signs `s`, which conjugates the rational points;
* the **standard space** `I_n = (1_n, 1)`, of signs `(1, …, 1)`, whose lattice is `𝓞_E^n`.

The matrix `J` of a space is hermitian and invertible, and the adelic matrices preserving the
form `x* J x` are exactly the elements of `G(s)`.

No CM type enters the definitions: at an infinite place `w` the conjugation of `E` extends to the
completion `E_w`, and read in `ℂ` through either embedding inducing `w` it is complex conjugation
(`NumberField.IsCMField.extensionEmbedding_infiniteAdeleRing_star_apply`), so the condition
`x* J x = diag(s)` at `w` is the same for both identifications of `E_w` with `ℂ`.

At the finite places the frame equation `x* J x = 1_n` is not a condition on each component of `x`
separately: its component at a finite place `w` reads `σ(x_{conj w})ᵀ J x_w = 1_n`, where
`σ : E_{conj w} ≃ E_w` extends the conjugation of `E`. When `w` does not split in `E / E⁺`,
`conj w = w` and this says that `x_w` is an isometry from the standard form to the form of `J`
over `E_w`. When `w` splits, `conj w ≠ w` and the equation couples the two components `x_w` and
`x_{conj w}`: it determines `x_{conj w}` from `x_w`, the equation at `conj w` being equivalent to
that at `w`.

## Main definitions

* `TauCeti.infiniteAdelicUnitaryGroup E s`, `TauCeti.adelicUnitaryGroup E s`: `G_∞(s)` and
  `G(s)`, with the finite component `TauCeti.adelicUnitaryGroup.finitePart : G(s) → G_f` and the
  embedding `TauCeti.adelicUnitaryGroup.ofFinite : G_f → G(s)`, `g ↦ (1, g)`.
* `TauCeti.FramedHermitianSpace E s`: the hermitian spaces with an adelic frame of signs `s`.
* `TauCeti.FramedHermitianSpace.rationalEmbedding`, `rationalPoints`, `finiteRationalPoints`:
  the embedding `γ ↦ x⁻¹ γ x` and the groups `Γ_V` and `Γ_{V,f}`.
* `TauCeti.FramedHermitianSpace.lattice`: the lattice `Λ_V`.
* The right action `V · g` of `G(s)`, as a `MulAction` of `G(s)ᵐᵒᵖ`.
* `TauCeti.FramedHermitianSpace.standard E ι`: the standard space `I_n`.

## Main results

* `TauCeti.exists_mem_adelicUnitaryGroup_iff`: an adelic matrix lies in `G(s)` exactly when it
  preserves the form `diag(s)` at the infinite places and `1_n` at the finite places.
* `TauCeti.FramedHermitianSpace.isHermitian_gram`, `TauCeti.FramedHermitianSpace.isUnit_gram`: the
  matrix `J` of a space is hermitian and invertible.
* `TauCeti.FramedHermitianSpace.rationalEmbedding_injective`: `γ ↦ x⁻¹ γ x` is injective.
* `TauCeti.FramedHermitianSpace.rationalPoints_smul`: `Γ_{V·g} = g⁻¹ Γ_V g`, and
  `TauCeti.FramedHermitianSpace.finiteRationalPoints_smul`: `Γ_{V·g, f} = g_f⁻¹ Γ_{V,f} g_f`.
* `TauCeti.FramedHermitianSpace.mem_lattice_standard_iff`: the lattice of `I_n` is `𝓞_E^n`.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §§2, 4.

## Attribution

The objects defined here follow `New.GInf`, `New.G`, `New.Space`, `New.Space.ratEmbed`,
`New.Space.Γ`, `New.Space.Γf`, `New.Space.baseLattice`, `New.stdSpace` and `New.Space.move`, and
the statements on the Gram matrix and on `G(s)` follow `New.Space.isUnit_J`,
`New.Space.isHermitian_J` and `New.G.ofMatrix`, in the files `src/Lib/Adelic/Unitary/Defs.lean`,
`src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean` and `src/Lib/Adelic/Unitary/GramMatrix.lean` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here is independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-! ### The adelic unitary group of a sign vector -/

/-- The archimedean adelic unitary group `G_∞(s) = U(diag s)(E_∞)` of a CM field `E` and a sign
vector `s`: the invertible matrices `g` over the infinite adeles with `g* diag(s) g = diag(s)`. As
conjugation acts within each infinite completion `E_w`, it is the product over the infinite places
`w` of the unitary groups `U(diag s)(E_w) ≅ U(p, n - p)`, `p` being the number of signs `+1`. -/
abbrev infiniteAdelicUnitaryGroup (s : ι → ℤˣ) : Subgroup (GL ι (InfiniteAdeleRing E)) :=
  unitaryGroupOf (diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E))

/-- The **adelic unitary group** `G(s) = G_∞(s) × G_f` of a CM field `E` and a sign vector `s`,
inside `GL_n(E_∞) × GL_n(𝔸_f) ≅ GL_n(𝔸)`: the adelic matrices preserving the form that is
`diag(s)` at every infinite place and `1_n` at every finite place. `Subgroup.prodEquiv`
identifies it with the product of `G_∞(s)` and `G_f`. -/
abbrev adelicUnitaryGroup (s : ι → ℤˣ) : Subgroup (GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) :=
  (infiniteAdelicUnitaryGroup E s).prod (finiteAdelicUnitaryGroup E ι)

/-- The finite component `G(s) → G_f`, `(g_∞, g_f) ↦ g_f`. -/
def adelicUnitaryGroup.finitePart (s : ι → ℤˣ) :
    adelicUnitaryGroup E s →* finiteAdelicUnitaryGroup E ι :=
  ((MonoidHom.snd _ _).comp (adelicUnitaryGroup E s).subtype).codRestrict _
    fun g ↦ g.property.2

/-- The embedding `G_f → G(s)`, `g ↦ (1, g)`. -/
def adelicUnitaryGroup.ofFinite (s : ι → ℤˣ) :
    finiteAdelicUnitaryGroup E ι →* adelicUnitaryGroup E s :=
  ((MonoidHom.inr _ _).comp (finiteAdelicUnitaryGroup E ι).subtype).codRestrict _
    fun g ↦ ⟨one_mem _, g.property⟩

variable {E}

/-- The finite component of `g ∈ G(s)` is `g_f`. -/
@[simp]
theorem adelicUnitaryGroup.coe_finitePart {s : ι → ℤˣ} (g : adelicUnitaryGroup E s) :
    (adelicUnitaryGroup.finitePart E s g : GL ι 𝔸ᶠ[E]) =
      (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2 :=
  (rfl)

/-- The embedding of `G_f` in `G(s)` is `g ↦ (1, g)`. -/
@[simp]
theorem adelicUnitaryGroup.coe_ofFinite {s : ι → ℤˣ} (g : finiteAdelicUnitaryGroup E ι) :
    (adelicUnitaryGroup.ofFinite E s g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) =
      (1, (g : GL ι 𝔸ᶠ[E])) :=
  (rfl)

/-- The finite component of `(1, g)` is `g`. -/
@[simp]
theorem adelicUnitaryGroup.finitePart_ofFinite {s : ι → ℤˣ} (g : finiteAdelicUnitaryGroup E ι) :
    adelicUnitaryGroup.finitePart E s (adelicUnitaryGroup.ofFinite E s g) = g :=
  (rfl)

/-- **The adelic matrices preserving the form are the elements of `G(s)`.** A pair `(M, N)` of
matrices over the infinite and the finite adeles is the adelic matrix of an element of `G(s)`
exactly when `M* diag(s) M = diag(s)` and `N* N = 1`; in particular such matrices are invertible. -/
theorem exists_mem_adelicUnitaryGroup_iff {s : ι → ℤˣ} {M : Matrix ι ι (InfiniteAdeleRing E)}
    {N : Matrix ι ι 𝔸ᶠ[E]} :
    (∃ g ∈ adelicUnitaryGroup E s,
        (g.1 : Matrix ι ι (InfiniteAdeleRing E)) = M ∧ (g.2 : Matrix ι ι 𝔸ᶠ[E]) = N) ↔
      star M * diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) * M =
          diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) ∧
        star N * N = 1 := by
  refine ⟨?_, fun ⟨hM, hN⟩ ↦ ?_⟩
  · rintro ⟨g, ⟨hg₁, hg₂⟩, rfl, rfl⟩
    exact ⟨mem_unitaryGroupOf_iff.1 hg₁, mem_finiteAdelicUnitaryGroup_iff.1 hg₂⟩
  · have hN' : star N * 1 * N = 1 := by rwa [Matrix.mul_one]
    have hs : IsUnit (diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) :=
      isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i ↦ (s i).isUnit.map (Int.castRingHom _))
    exact ⟨((unitaryGroupOf.ofMatrix hs M hM : GL ι _),
      (unitaryGroupOf.ofMatrix isUnit_one N hN' : GL ι _)),
      ⟨(unitaryGroupOf.ofMatrix _ M hM).property, (unitaryGroupOf.ofMatrix _ N hN').property⟩,
      unitaryGroupOf.val_ofMatrix _ _ _, unitaryGroupOf.val_ofMatrix _ _ _⟩

/-! ### Hermitian spaces with an adelic frame -/

variable (E) in
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
  /-- At the infinite places the frame carries the form of `J` to that of `diag(s)`. -/
  star_mul_gram_mul_fst : star (frame.1 : Matrix ι ι (InfiniteAdeleRing E)) *
      gram.map (algebraMap E (InfiniteAdeleRing E)) * frame.1 =
    diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)
  /-- At the finite places the frame carries the form of `J` to the standard form. -/
  star_mul_gram_mul_snd :
    star (frame.2 : Matrix ι ι 𝔸ᶠ[E]) * gram.map (algebraMap E 𝔸ᶠ[E]) * frame.2 = 1

namespace FramedHermitianSpace

variable {s : ι → ℤˣ} (V : FramedHermitianSpace E s)

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

/-- **The Gram matrix of a space with an adelic frame is invertible**: its image over the finite
adeles is carried to `1_n` by the frame. -/
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

/-- The conjugate `x⁻¹ γ x` of a rational unitary matrix `γ ∈ U(J)(E⁺)` by the frame lies in
`G(s)`. -/
private theorem conj_mem_adelicUnitaryGroup {γ : GL ι E} (hγ : γ ∈ unitaryGroupOf V.gram) :
    (V.frame.1⁻¹ * GeneralLinearGroup.map (algebraMap E (InfiniteAdeleRing E)) γ * V.frame.1,
      V.frame.2⁻¹ * GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ * V.frame.2) ∈
        adelicUnitaryGroup E s := by
  refine ⟨inv_mul_mul_mem_unitaryGroupOf V.star_mul_gram_mul_fst ?_, ?_⟩
  · exact map_mem_unitaryGroupOf (fun x ↦ algebraMap_star_comm x) hγ
  · refine inv_mul_mul_mem_unitaryGroupOf V.star_mul_gram_mul_snd ?_
    exact map_mem_unitaryGroupOf (fun x ↦ algebraMap_star_comm x) hγ

/-- The **rational embedding** `γ ↦ x⁻¹ γ x` of the group `U(J)(E⁺) = {γ ∈ GL_n(E) : γ* J γ = J}`
of rational points of the unitary group of the Gram matrix in the adelic unitary group `G(s)`,
`γ` being read diagonally in `GL_n(𝔸)`. -/
def rationalEmbedding : unitaryGroupOf V.gram →* adelicUnitaryGroup E s where
  toFun γ := ⟨(V.frame.1⁻¹ * GeneralLinearGroup.map (algebraMap E (InfiniteAdeleRing E)) γ *
      V.frame.1, V.frame.2⁻¹ * GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ * V.frame.2),
    V.conj_mem_adelicUnitaryGroup γ.property⟩
  map_one' := by ext : 2 <;> simp
  map_mul' γ δ := by ext : 2 <;> simp [mul_assoc]

/-- The rational embedding is `γ ↦ x⁻¹ γ x`. -/
@[simp]
theorem coe_rationalEmbedding (γ : unitaryGroupOf V.gram) :
    (V.rationalEmbedding γ : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) =
      (V.frame.1⁻¹ * GeneralLinearGroup.map (algebraMap E (InfiniteAdeleRing E)) γ * V.frame.1,
        V.frame.2⁻¹ * GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ * V.frame.2) :=
  (rfl)

/-- The rational embedding is injective. -/
theorem rationalEmbedding_injective : Function.Injective V.rationalEmbedding := by
  intro γ δ h
  have h₂ := congrArg (fun g ↦ (adelicUnitaryGroup.finitePart E s g : GL ι 𝔸ᶠ[E])) h
  simp only [adelicUnitaryGroup.coe_finitePart, coe_rationalEmbedding, mul_left_inj,
    mul_right_inj] at h₂
  exact Subtype.ext (GeneralLinearGroup.map_injective
    (FiniteAdeleRing.algebraMap_injective E (RingOfIntegers.not_isField E)) h₂)

/-- The **rational points** `Γ_V` of a space with an adelic frame: the image of `U(J)(E⁺)` in the
adelic unitary group `G(s)` under the rational embedding `γ ↦ x⁻¹ γ x`. -/
def rationalPoints : Subgroup (adelicUnitaryGroup E s) :=
  V.rationalEmbedding.range

/-- The **finite rational points** `Γ_{V,f}` of a space with an adelic frame: the image of its
rational points `Γ_V` in the finite adelic unitary group `G_f`. -/
def finiteRationalPoints : Subgroup (finiteAdelicUnitaryGroup E ι) :=
  V.rationalPoints.map (adelicUnitaryGroup.finitePart E s)

/-- `Γ_{V,f}` consists of the conjugates `x_f⁻¹ γ x_f` of the elements `γ ∈ U(J)(E⁺)` by the
finite component `x_f` of the frame. -/
theorem mem_finiteRationalPoints_iff {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ V.finiteRationalPoints ↔ ∃ γ : unitaryGroupOf V.gram,
      V.frame.2⁻¹ * GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ * V.frame.2 =
        (g : GL ι 𝔸ᶠ[E]) := by
  refine ⟨?_, fun ⟨γ, hγ⟩ ↦ ⟨V.rationalEmbedding γ, ⟨γ, rfl⟩, Subtype.ext hγ⟩⟩
  rintro ⟨_, ⟨γ, rfl⟩, rfl⟩
  exact ⟨γ, rfl⟩

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
      FiniteAdeleRing.integralAdeles (𝓞 E) E :=
  Submodule.mem_pi.trans ⟨fun h i ↦ h i (Set.mem_univ i), fun h i _ ↦ h i⟩

/-! ### The moved space -/

/-- The right action of the adelic unitary group `G(s)` on the spaces with an adelic frame of
signs `s`: the **moved space** `V · g = (J, x g)`. -/
instance : MulAction (adelicUnitaryGroup E s)ᵐᵒᵖ (FramedHermitianSpace E s) where
  smul g V :=
    { gram := V.gram
      frame := V.frame * g.unop
      star_mul_gram_mul_fst :=
        star_mul_mul_mul_eq_of_mem_unitaryGroupOf V.star_mul_gram_mul_fst g.unop.property.1
      star_mul_gram_mul_snd :=
        star_mul_mul_mul_eq_of_mem_unitaryGroupOf V.star_mul_gram_mul_snd g.unop.property.2 }
  one_smul V := FramedHermitianSpace.ext rfl (mul_one V.frame)
  mul_smul _ _ _ := FramedHermitianSpace.ext rfl (mul_assoc _ _ _).symm

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
  rw [rationalPoints, rationalPoints, MonoidHom.map_range]
  exact congrArg MonoidHom.range (MonoidHom.ext (V.rationalEmbedding_smul g))

/-- **Finite rational points of a moved space**: `Γ_{V·g, f} = g_f⁻¹ Γ_{V,f} g_f`, for `g_f` the
finite component of `g`. -/
theorem finiteRationalPoints_smul (g : (adelicUnitaryGroup E s)ᵐᵒᵖ) :
    (g • V).finiteRationalPoints = V.finiteRationalPoints.map
      (MulAut.conj (adelicUnitaryGroup.finitePart E s g.unop)⁻¹).toMonoidHom := by
  rw [finiteRationalPoints, finiteRationalPoints, rationalPoints_smul, Subgroup.map_map,
    Subgroup.map_map]
  -- the finite component of `g⁻¹ h g` is `g_f⁻¹ h_f g_f`
  exact congrArg V.rationalPoints.map (MonoidHom.ext fun h ↦ by simp)

/-- Moving a space by an element of `G(s)` whose finite component lies in
`K₀ = G_f ∩ GL_n(Ô)` does not change its lattice. -/
theorem lattice_smul_of_mem_integralAdelicUnitaryGroup (g : (adelicUnitaryGroup E s)ᵐᵒᵖ)
    (hg : adelicUnitaryGroup.finitePart E s g.unop ∈ integralAdelicUnitaryGroup E ι) :
    (g • V).lattice = V.lattice := by
  -- An integral matrix carries integral vectors to integral vectors.
  have hint (k : finiteAdelicUnitaryGroup E ι) (hk : k ∈ integralAdelicUnitaryGroup E ι)
      (v : ι → 𝔸ᶠ[E]) (hv : ∀ i, v i ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E) (i : ι) :
      (((k : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ v) i ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E :=
    Subalgebra.sum_mem _ fun j _ ↦
      Subalgebra.mul_mem _ (mem_integralAdelicUnitaryGroup_iff.1 hk i j) (hv j)
  ext y
  rw [mem_lattice_iff, mem_lattice_iff, frame_smul, Prod.snd_mul, _root_.mul_inv_rev,
    Units.val_mul, ← mulVec_mulVec]
  refine ⟨fun h i ↦ ?_, fun h ↦ hint _ (inv_mem hg) _ h⟩
  have := hint _ hg _ h i
  rwa [adelicUnitaryGroup.coe_finitePart, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, one_mulVec] at this

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
theorem standard_gram : (standard E ι).gram = 1 :=
  (rfl)

/-- The frame of the standard space is `1`. -/
@[simp]
theorem standard_frame : (standard E ι).frame = 1 :=
  (rfl)

/-- The rational embedding of the standard space is the diagonal embedding of `U(1_n)(E⁺)`. -/
theorem coe_rationalEmbedding_standard (γ : unitaryGroupOf (standard E ι).gram) :
    ((standard E ι).rationalEmbedding γ : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) =
      (GeneralLinearGroup.map (algebraMap E (InfiniteAdeleRing E)) γ,
        GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ) := by
  simp

/-- **The lattice of the standard space is `𝓞_E^n`.** -/
theorem mem_lattice_standard_iff {y : ι → E} :
    y ∈ (standard E ι).lattice ↔ ∀ i, y i ∈ (algebraMap (𝓞 E) E).range := by
  simp [mem_lattice_iff, FiniteAdeleRing.algebraMap_mem_integralAdeles_iff]

end FramedHermitianSpace

end TauCeti
