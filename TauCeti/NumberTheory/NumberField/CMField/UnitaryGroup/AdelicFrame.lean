/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.ChangeOfFrame
public import TauCeti.NumberTheory.NumberField.CMField.AdelicLattice
public import TauCeti.NumberTheory.NumberField.CMType.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.NumberTheory.NumberField.CMField.Basic

/-!
# Hermitian spaces with an adelic frame and their unitary groups

Let `E` be a CM field with complex conjugation `x ↦ conj x`, `Φ` a CM type of `E` (one complex
embedding for each infinite place), `𝔸_f` the finite adeles of `E` with the involution induced by
conjugation, `Ô` the integral finite adeles and `n` a natural number. Matrices are conjugate
transposed by `g* = star g`, and `U(J)(R) = {g ∈ GL_n(R) : g* J g = J}` is
`Matrix.unitaryGroupOf J`. Through `Φ`, the adeles of `E` are `ℂ^Φ × 𝔸_f`, so an element of
`GL_n` of the adeles is a family of matrices in `GL_n(ℂ)`, one for each `φ ∈ Φ`, together with a
matrix in `GL_n(𝔸_f)`. This file sets up the adelic unitary groups and the spaces on which the
automorphic forms of unitary groups over `E` live.

* `G_f = U(1_n)(𝔸_f)`, the unitary group of the standard form over the finite adeles
  (`TauCeti.finiteAdelicUnitaryGroup`), with its subgroup `K₀ = G_f ∩ GL_n(Ô)`
  (`TauCeti.integralFiniteAdelicUnitaryGroup`), which is open. A *level* is an open subgroup of
  `G_f` contained in `K₀` (`TauCeti.IsUnitaryLevel`).
* For a sign vector `s ∈ {±1}^n`, the same at every infinite place,
  `G_∞(s) = ∏_{φ ∈ Φ} U(diag s)(ℂ)` (`TauCeti.InfiniteUnitaryGroup`), each factor isomorphic to
  `U(p, n - p)` for `p = #{i : s_i = 1}`, and `G(s) = G_∞(s) × G_f` (`TauCeti.AdelicUnitaryGroup`).
* A *hermitian space with an adelic frame of signs `s`* (`TauCeti.AdelicHermitianSpace`) is a
  matrix `J ∈ M_n(E)` together with a frame `x` in `GL_n` of the adeles such that `x* J x = diag(s)`
  at every `φ ∈ Φ` (with `J` read through `φ`) and `x* J x = 1_n` over `𝔸_f`. So the hermitian form
  `h_J(u, v) = ū^T J v` on `E^n` has signature `(p, n - p)` at every infinite place and is isometric
  to the standard form at every finite place; `J` is hermitian
  (`TauCeti.AdelicHermitianSpace.isHermitian_gram`).
* Its *rational points*: `γ ↦ x⁻¹ γ x` embeds the unitary group `U(J)(E⁺)` of `h_J`, the group of
  `γ ∈ GL_n(E)` with `γ* J γ = J`, into `G(s)` (`TauCeti.AdelicHermitianSpace.ratEmbedding`,
  injective by `TauCeti.AdelicHermitianSpace.ratEmbedding_injective`). Its image is `Γ_V`
  (`TauCeti.AdelicHermitianSpace.ratPoints`) and the image of `Γ_V` in `G_f` is `Γ_{V,f}`
  (`TauCeti.AdelicHermitianSpace.finiteRatPoints`).
* The *moved space* `V·g = (J, x g)` for `g ∈ G(s)` (`TauCeti.AdelicHermitianSpace.move`), a right
  action of `G(s)` (`TauCeti.AdelicHermitianSpace.move_one`,
  `TauCeti.AdelicHermitianSpace.move_move`) for which `Γ_{V·g} = g⁻¹ Γ_V g`
  (`TauCeti.AdelicHermitianSpace.mem_ratPoints_move_iff`), and the *standard space*
  `I_n = (1_n, 1)` of signs `(1, …, 1)` (`TauCeti.AdelicHermitianSpace.standard`).

## References

* M. Harris, S. S. Kudla and W. J. Sweet, *Theta dichotomy for unitary groups*,
  J. Amer. Math. Soc. 9 (1996), §1, for hermitian spaces over a quadratic extension of number
  fields and their unitary groups.
* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), §§1–4, for levels and the
  definite case.

## Attribution

The declarations correspond to those of `src/Lib/Adelic/Unitary/Defs.lean` (`New.Gf`, `New.G`,
`New.GInf`, `New.stdLevel`, `New.IsLevel`, `New.Space`, `New.Space.ratEmbed`, `New.Space.Γ`,
`New.Space.Γf`, `New.stdSpace`) and `src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean`
(`New.Space.move`) of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC). There `E` also contains a primitive root of unity of order `5040`; nothing here
needs it.
-/

public section
noncomputable section

open Matrix IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

/-! ### The finite adelic unitary group and levels -/

/-- The **finite adelic unitary group** `G_f = U(1_n)(𝔸_f)` of a CM field `E`: the matrices
`g ∈ GL_n(𝔸_f)` with `g* g = 1`, for the conjugate transpose `g* = star g` of complex conjugation
on the finite adeles. -/
abbrev finiteAdelicUnitaryGroup : Subgroup (GL (Fin n) 𝔸ᶠ[E]) :=
  unitaryGroupOf 1

variable {E n} in
/-- Membership in `G_f` is the equation `g* g = 1`. -/
theorem mem_finiteAdelicUnitaryGroup_iff {g : GL (Fin n) 𝔸ᶠ[E]} :
    g ∈ finiteAdelicUnitaryGroup E n ↔ star (g : Matrix (Fin n) (Fin n) 𝔸ᶠ[E]) * g = 1 := by
  rw [mem_unitaryGroupOf_iff, Matrix.mul_one]

/-- The **integral finite adelic unitary group** `K₀ = G_f ∩ GL_n(Ô)`, as a subgroup of `G_f`. -/
def integralFiniteAdelicUnitaryGroup : Subgroup (finiteAdelicUnitaryGroup E n) :=
  (integralGL (R := 𝓞 E) E n).range.comap (finiteAdelicUnitaryGroup E n).subtype

variable {E n}

/-- An element of `G_f` lies in `K₀` exactly when it lies in `GL_n(Ô)`. -/
@[simp]
theorem mem_integralFiniteAdelicUnitaryGroup_iff {g : finiteAdelicUnitaryGroup E n} :
    g ∈ integralFiniteAdelicUnitaryGroup E n ↔
      (g : GL (Fin n) 𝔸ᶠ[E]) ∈ (integralGL (R := 𝓞 E) E n).range :=
  Iff.rfl

/-- An element of `G_f` lies in `K₀` exactly when its entries and the entries of its inverse are
integral. -/
theorem mem_integralFiniteAdelicUnitaryGroup_iff_forall {g : finiteAdelicUnitaryGroup E n} :
    g ∈ integralFiniteAdelicUnitaryGroup E n ↔
      (∀ i j, ((g : GL (Fin n) 𝔸ᶠ[E]) : Matrix (Fin n) (Fin n) 𝔸ᶠ[E]) i j ∈
        integralAdeles (𝓞 E) E) ∧
      ∀ i j, (↑(g : GL (Fin n) 𝔸ᶠ[E])⁻¹ : Matrix (Fin n) (Fin n) 𝔸ᶠ[E]) i j ∈
        integralAdeles (𝓞 E) E := by
  rw [mem_integralFiniteAdelicUnitaryGroup_iff, mem_range_integralGL_iff]

variable (E n) in
/-- `K₀` is open in `G_f`, since `GL_n(Ô)` is open in `GL_n(𝔸_f)`. -/
theorem isOpen_integralFiniteAdelicUnitaryGroup :
    IsOpen (integralFiniteAdelicUnitaryGroup E n : Set (finiteAdelicUnitaryGroup E n)) :=
  (isOpenEmbedding_integralGL (R := 𝓞 E) E n).isOpen_range.preimage continuous_subtypeVal

/-- A **level** of the finite adelic unitary group: an open subgroup `K` of `G_f` contained in
`K₀ = G_f ∩ GL_n(Ô)`. -/
def IsUnitaryLevel (K : Subgroup (finiteAdelicUnitaryGroup E n)) : Prop :=
  IsOpen (K : Set (finiteAdelicUnitaryGroup E n)) ∧ K ≤ integralFiniteAdelicUnitaryGroup E n

theorem isUnitaryLevel_iff {K : Subgroup (finiteAdelicUnitaryGroup E n)} :
    IsUnitaryLevel K ↔
      IsOpen (K : Set (finiteAdelicUnitaryGroup E n)) ∧ K ≤ integralFiniteAdelicUnitaryGroup E n :=
  Iff.rfl

variable (E n) in
/-- `K₀` itself is a level. -/
theorem isUnitaryLevel_integralFiniteAdelicUnitaryGroup :
    IsUnitaryLevel (integralFiniteAdelicUnitaryGroup E n) :=
  ⟨isOpen_integralFiniteAdelicUnitaryGroup E n, le_rfl⟩

/-- The intersection of two levels is a level. -/
theorem IsUnitaryLevel.inf {K L : Subgroup (finiteAdelicUnitaryGroup E n)} (hK : IsUnitaryLevel K)
    (hL : IsUnitaryLevel L) : IsUnitaryLevel (K ⊓ L) :=
  ⟨hK.1.inter hL.1, inf_le_left.trans hK.2⟩

/-- An open subgroup of a level is a level. -/
theorem IsUnitaryLevel.of_le {K L : Subgroup (finiteAdelicUnitaryGroup E n)} (hL : IsUnitaryLevel L)
    (hK : IsOpen (K : Set (finiteAdelicUnitaryGroup E n))) (hKL : K ≤ L) : IsUnitaryLevel K :=
  ⟨hK, hKL.trans hL.2⟩

/-! ### The archimedean and the adelic unitary groups -/

variable (n) in
/-- The **archimedean unitary group** `G_∞(s) = ∏_{φ ∈ Φ} U(diag s)(ℂ)` of signs `s ∈ {±1}^n`
(the same at every infinite place), indexed by the embeddings of a CM type `Φ`, that is by the
infinite places of `E`. Each factor is isomorphic to `U(p, n - p)` for `p = #{i : s_i = 1}`. -/
abbrev InfiniteUnitaryGroup (Φ : CMType E) (s : Fin n → ℤˣ) : Type _ :=
  Φ → unitaryGroupOf (diagonal fun i ↦ ((s i : ℤ) : ℂ))

variable (n) in
/-- The **adelic unitary group** `G(s) = G_∞(s) × G_f` of signs `s`, read through the CM type
`Φ`. -/
abbrev AdelicUnitaryGroup (Φ : CMType E) (s : Fin n → ℤˣ) : Type _ :=
  InfiniteUnitaryGroup n Φ s × finiteAdelicUnitaryGroup E n

/-! ### Hermitian spaces with an adelic frame -/

/-- A **hermitian space with an adelic frame of signs `s`** over a CM field `E` with CM type `Φ`:
a Gram matrix `J ∈ M_n(E)` with a frame `x = ((x_φ)_{φ ∈ Φ}, x_f)` in `GL_n(ℂ)^Φ × GL_n(𝔸_f)`
such that `x_φ* J x_φ = diag(s)` for every `φ ∈ Φ`, with `J` read through `φ`, and
`x_f* J x_f = 1_n`. The hermitian form `h_J(u, v) = ū^T J v` on `E^n` then has signature
`(p, n - p)`, `p = #{i : s_i = 1}`, at every infinite place, and is standard at every finite
place. -/
@[ext]
structure AdelicHermitianSpace (Φ : CMType E) (s : Fin n → ℤˣ) where
  /-- The Gram matrix `J` of the hermitian form. -/
  gram : Matrix (Fin n) (Fin n) E
  /-- The components `x_φ ∈ GL_n(ℂ)` of the frame at the infinite places. -/
  frameInf : Φ → GL (Fin n) ℂ
  /-- The component `x_f ∈ GL_n(𝔸_f)` of the frame at the finite places. -/
  frameFin : GL (Fin n) 𝔸ᶠ[E]
  /-- At every `φ ∈ Φ` the frame carries `J` to `diag(s)`. -/
  star_frameInf_mul_mul (φ : Φ) :
    star (frameInf φ : Matrix (Fin n) (Fin n) ℂ) * gram.map (φ : E →+* ℂ) * frameInf φ =
      diagonal fun i ↦ ((s i : ℤ) : ℂ)
  /-- Over the finite adeles the frame carries `J` to `1_n`. -/
  star_frameFin_mul_mul :
    star (frameFin : Matrix (Fin n) (Fin n) 𝔸ᶠ[E]) * gram.map (algebraMap E 𝔸ᶠ[E]) * frameFin = 1

namespace AdelicHermitianSpace

variable {Φ : CMType E} {s : Fin n → ℤˣ} (V : AdelicHermitianSpace Φ s)

/-- The Gram matrix of a space with an adelic frame is hermitian: over the finite adeles it is
`(x_f⁻¹)* x_f⁻¹`. -/
theorem isHermitian_gram : V.gram.IsHermitian := by
  have h := star_inv_mul_mul_inv_eq V.star_frameFin_mul_mul
  rw [Matrix.mul_one] at h
  refine Matrix.map_injective (algebraMap_injective E (RingOfIntegers.not_isField E)) ?_
  dsimp only
  rw [conjTranspose_map _ fun x ↦ (star_algebraMap x).symm, ← h, ← star_eq_conjTranspose,
    star_mul, star_star]

/-! #### Rational points -/

/-- The **embedding of the rational points**: `γ ↦ x⁻¹ γ x` from the unitary group
`U(J)(E⁺) = {γ ∈ GL_n(E) : γ* J γ = J}` of the hermitian form into `G(s)`, with `γ` read through
each `φ ∈ Φ` at the infinite places and in `𝔸_f` at the finite places. -/
def ratEmbedding : unitaryGroupOf V.gram →* AdelicUnitaryGroup n Φ s :=
  (MonoidHom.pi fun φ : Φ ↦
    (unitaryGroupOf.conjEquiv (V.frameInf φ) (V.star_frameInf_mul_mul φ)).toMonoidHom.comp
      (unitaryGroupOf.mapHom V.gram (φ : E →+* ℂ) fun x ↦ complexEmbedding_star _ x)).prod
  ((unitaryGroupOf.conjEquiv V.frameFin V.star_frameFin_mul_mul).toMonoidHom.comp
    (unitaryGroupOf.mapHom V.gram (algebraMap E 𝔸ᶠ[E]) fun x ↦ (star_algebraMap x).symm))

/-- The component at `φ ∈ Φ` of the image of a rational point `γ` is `x_φ⁻¹ φ(γ) x_φ`. -/
@[simp]
theorem coe_ratEmbedding_fst_apply (γ : unitaryGroupOf V.gram) (φ : Φ) :
    ((V.ratEmbedding γ).1 φ : GL (Fin n) ℂ) =
      (V.frameInf φ)⁻¹ * GeneralLinearGroup.map (φ : E →+* ℂ) (γ : GL (Fin n) E) *
        V.frameInf φ := by
  rw [ratEmbedding, MonoidHom.prod_apply]
  simp

/-- The finite component of the image of a rational point `γ` is `x_f⁻¹ γ x_f`. -/
@[simp]
theorem coe_ratEmbedding_snd (γ : unitaryGroupOf V.gram) :
    ((V.ratEmbedding γ).2 : GL (Fin n) 𝔸ᶠ[E]) =
      V.frameFin⁻¹ * GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) (γ : GL (Fin n) E) *
        V.frameFin := by
  simp [ratEmbedding]

/-- The embedding of the rational points is injective. -/
theorem ratEmbedding_injective : Function.Injective V.ratEmbedding := fun γ δ h ↦ by
  have h' := congrArg (fun g : AdelicUnitaryGroup n Φ s ↦ (g.2 : GL (Fin n) 𝔸ᶠ[E])) h
  simp only [coe_ratEmbedding_snd, mul_left_inj, mul_right_inj] at h'
  exact Subtype.ext
    (GeneralLinearGroup.map_injective (algebraMap_injective E (RingOfIntegers.not_isField E)) h')

/-- The group `Γ_V ⊆ G(s)` of **rational points** of a space with an adelic frame: the image of
the unitary group of its hermitian form under `γ ↦ x⁻¹ γ x`. -/
def ratPoints : Subgroup (AdelicUnitaryGroup n Φ s) :=
  V.ratEmbedding.range

@[simp]
theorem mem_ratPoints_iff {g : AdelicUnitaryGroup n Φ s} :
    g ∈ V.ratPoints ↔ ∃ γ, V.ratEmbedding γ = g :=
  MonoidHom.mem_range

/-- The group `Γ_{V,f} ⊆ G_f` of **finite rational points**: the image of `Γ_V` in `G_f`. -/
def finiteRatPoints : Subgroup (finiteAdelicUnitaryGroup E n) :=
  V.ratPoints.map (MonoidHom.snd _ _)

@[simp]
theorem mem_finiteRatPoints_iff {g : finiteAdelicUnitaryGroup E n} :
    g ∈ V.finiteRatPoints ↔ ∃ γ, (V.ratEmbedding γ).2 = g := by
  rw [finiteRatPoints, Subgroup.mem_map]
  exact ⟨fun ⟨_, ⟨γ, hγ⟩, hx⟩ ↦ ⟨γ, hγ ▸ hx⟩, fun ⟨γ, hγ⟩ ↦ ⟨_, ⟨γ, rfl⟩, hγ⟩⟩

/-! #### Moving a space -/

/-- The **moved space** `V·g = (J, x g)` of a space `V = (J, x)` with an adelic frame of signs `s`,
for `g ∈ G(s)`. The body is exposed so that the Gram matrix of `V·g` is definitionally that of
`V`, which lets the rational points `unitaryGroupOf V.gram` of `V` serve as those of `V·g` (as in
`TauCeti.AdelicHermitianSpace.ratEmbedding_move`). -/
@[expose] def move (g : AdelicUnitaryGroup n Φ s) : AdelicHermitianSpace Φ s where
  gram := V.gram
  frameInf φ := V.frameInf φ * (g.1 φ : GL (Fin n) ℂ)
  frameFin := V.frameFin * (g.2 : GL (Fin n) 𝔸ᶠ[E])
  star_frameInf_mul_mul φ :=
    unitaryGroupOf.star_mul_mul_mul_eq (V.star_frameInf_mul_mul φ)
      (mem_unitaryGroupOf_iff.mp (g.1 φ).property)
  star_frameFin_mul_mul :=
    unitaryGroupOf.star_mul_mul_mul_eq V.star_frameFin_mul_mul
      (mem_unitaryGroupOf_iff.mp g.2.property)

@[simp]
theorem gram_move (g : AdelicUnitaryGroup n Φ s) : (V.move g).gram = V.gram :=
  (rfl)

@[simp]
theorem frameInf_move (g : AdelicUnitaryGroup n Φ s) (φ : Φ) :
    (V.move g).frameInf φ = V.frameInf φ * (g.1 φ : GL (Fin n) ℂ) :=
  (rfl)

@[simp]
theorem frameFin_move (g : AdelicUnitaryGroup n Φ s) :
    (V.move g).frameFin = V.frameFin * (g.2 : GL (Fin n) 𝔸ᶠ[E]) :=
  (rfl)

/-- Moving by `1` does not change a space. -/
@[simp]
theorem move_one : V.move 1 = V := by
  ext <;> simp

/-- Moving is a right action of `G(s)`: `(V·g)·h = V·(g h)`. -/
@[simp]
theorem move_move (g h : AdelicUnitaryGroup n Φ s) : (V.move g).move h = V.move (g * h) := by
  ext <;> simp [mul_assoc]

/-- The rational points of the moved space `V·g` are those of `V` conjugated by `g`. -/
theorem ratEmbedding_move (g : AdelicUnitaryGroup n Φ s) (γ : unitaryGroupOf V.gram) :
    (V.move g).ratEmbedding γ = g⁻¹ * V.ratEmbedding γ * g := by
  refine Prod.ext (funext fun φ ↦ Subtype.ext ?_) (Subtype.ext ?_)
  · rw [(V.move g).coe_ratEmbedding_fst_apply γ φ]
    simp only [coe_ratEmbedding_fst_apply, frameInf_move, Prod.fst_mul, Prod.fst_inv,
      Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
    group
  · rw [(V.move g).coe_ratEmbedding_snd γ]
    simp only [coe_ratEmbedding_snd, frameFin_move, Prod.snd_mul, Prod.snd_inv,
      Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
    group

/-- `Γ_{V·g} = g⁻¹ Γ_V g`. -/
theorem mem_ratPoints_move_iff (g x : AdelicUnitaryGroup n Φ s) :
    x ∈ (V.move g).ratPoints ↔ g * x * g⁻¹ ∈ V.ratPoints := by
  simp only [mem_ratPoints_iff]
  refine exists_congr fun γ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, V.ratEmbedding_move g γ]
    group
  · rw [V.ratEmbedding_move g γ, h]
    group

/-! #### The standard space -/

variable (Φ n) in
/-- The **standard space** `I_n = (1_n, 1)` of signs `(1, …, 1)`: the standard definite hermitian
form `h(u, v) = ū^T v` with the identity frame. -/
def standard : AdelicHermitianSpace Φ (fun _ : Fin n ↦ 1) where
  gram := 1
  frameInf _ := 1
  frameFin := 1
  star_frameInf_mul_mul _ := by simp
  star_frameFin_mul_mul := by simp

variable (Φ n)

@[simp]
theorem gram_standard : (standard n Φ).gram = 1 :=
  (rfl)

@[simp]
theorem frameInf_standard (φ : Φ) : (standard n Φ).frameInf φ = 1 :=
  (rfl)

@[simp]
theorem frameFin_standard : (standard n Φ).frameFin = 1 :=
  (rfl)

end AdelicHermitianSpace

end TauCeti
