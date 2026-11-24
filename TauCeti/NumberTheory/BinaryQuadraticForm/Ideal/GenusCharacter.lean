/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.GenusCharacter
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Composition
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.PicEquivalence
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Narrow.Composition
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Narrow.Equivalence

/-!
# Genus characters on the class groups of quadratic orders

A genus character `χ` of discriminant `D` (`IsGenusChar D χ`) takes one value on the values
prime to its modulus of a primitive form of discriminant `D`, and that value is an invariant of
the proper class and multiplicative under Dirichlet composition. Through the dictionary between
proper classes of forms and invertible ideals of the order `𝒪_D` of discriminant `D`, it is
therefore a homomorphism on the class group of `𝒪_D`, with values squaring to `1`:

* `TauCeti.BinaryQuadraticForm.picGenusChar` on `Pic 𝒪_D` for `D = -n < 0`, through the proper
  classes of primitive positive definite forms (`posDefProperClassToPic`);
* `TauCeti.BinaryQuadraticForm.narrowPicGenusChar` on `NarrowPic 𝒪_D` for nonsquare `D > 0`,
  through all proper classes of primitive forms (`properClassEquivNarrowPic`).

Each sends the class of a form `f` to `genusChar χ f` (`picGenusChar_picClass`,
`narrowPicGenusChar_narrowPicClass`), and is trivial on squares (`picGenusChar_sq`,
`narrowPicGenusChar_sq`). They are meant as the coordinates of Gauss's genus map, whose kernel,
the principal genus, then contains the squares; that map and the genera are not set up here.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §3.B, Theorem 3.15.
-/

public section

open MulAction
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields

variable {m : ℕ} {R : Type*} [CommMonoidWithZero R] {χ : MulChar (ZMod m) R}

section Transport

variable {D : ℤ} {S : SubMulAction SL(2, ℤ) (BinaryQuadraticForm ℤ)}
  (hS : ∀ f ∈ S, f.discrim = D ∧ f.IsPrimitive) (hχ : IsGenusChar D χ)
  {G : Type*} [Monoid G] (F : orbitRel.Quotient SL(2, ℤ) S ≃ G)

include hS hχ in
/-- The genus character of a representative of a proper class is that of any form in it. -/
private theorem genusChar_out_mk (f : S) :
    genusChar χ ((Quotient.mk _ f : orbitRel.Quotient SL(2, ℤ) S).out : BinaryQuadraticForm ℤ) =
      genusChar χ f := by
  have hfχ : IsGenusChar (f : BinaryQuadraticForm ℤ).discrim χ := by
    rwa [(hS f f.property).1]
  obtain ⟨γ, hγ⟩ := Quotient.mk_out (s := orbitRel SL(2, ℤ) S) f
  rw [← hγ, SubMulAction.val_smul, hfχ.genusChar_smul]

/-- `F` sends Dirichlet compositions to products: any two proper classes in `S` have
representatives `(a, B, a'C)` and `(a', B, aC)` whose composition `(aa', B, C)` lies in `S`, with
class sent by `F` to the product of their images. -/
private def MapsCompositionToMul : Prop :=
  ∀ q₁ q₂, ∃ (a a' B C : ℤ) (f g h : S), Quotient.mk _ f = q₁ ∧ Quotient.mk _ g = q₂ ∧
      (f : BinaryQuadraticForm ℤ) = ⟨a, B, a' * C⟩ ∧ (g : BinaryQuadraticForm ℤ) = ⟨a', B, a * C⟩ ∧
      (h : BinaryQuadraticForm ℤ) = ⟨a * a', B, C⟩ ∧ F q₁ * F q₂ = F (Quotient.mk _ h)

/-- The genus character transported along a bijection `F` from the proper classes in `S` to a
monoid, which sends the principal class to `1` and Dirichlet compositions to products. -/
private noncomputable def genusCharHom (p : S) (hp : (p : BinaryQuadraticForm ℤ) = principalForm D)
    (hFp : F (Quotient.mk _ p) = 1)
    (hF : MapsCompositionToMul F) [NeZero m] : G →* R where
  toFun c := genusChar χ (F.symm c).out
  map_one' := by
    rw [F.symm_apply_eq.mpr hFp.symm, genusChar_out_mk hS hχ, hp, hχ.genusChar_principalForm]
  map_mul' c₁ c₂ := by
    obtain ⟨a, a', B, C, f, g, h, hf, hg, hfe, hge, hhe, hmul⟩ := hF (F.symm c₁) (F.symm c₂)
    rw [F.apply_symm_apply, F.apply_symm_apply] at hmul
    rw [F.symm_apply_eq.mpr hmul, ← hf, ← hg, genusChar_out_mk hS hχ, genusChar_out_mk hS hχ,
      genusChar_out_mk hS hχ, hfe, hge, hhe]
    refine IsGenusChar.genusChar_mk_mul (by rwa [← hhe, (hS h h.property).1]) ?_ ?_
    · exact hfe ▸ (hS f f.property).2.exists_isUnit_eval (NeZero.ne m)
    · exact hge ▸ (hS g g.property).2.exists_isUnit_eval (NeZero.ne m)

variable {F} {p : S} {hp : (p : BinaryQuadraticForm ℤ) = principalForm D}
  {hFp : F (Quotient.mk _ p) = 1}
  [NeZero m]

private theorem genusCharHom_apply_mk {hF : MapsCompositionToMul F} (f : S) :
    genusCharHom hS hχ F p hp hFp hF (F (Quotient.mk _ f)) = genusChar χ f := by
  rw [genusCharHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.symm_apply_apply]
  exact genusChar_out_mk hS hχ f

private theorem genusCharHom_sq {hF : MapsCompositionToMul F} (c : G) :
    genusCharHom hS hχ F p hp hFp hF (c ^ 2) = 1 := by
  obtain ⟨q, rfl⟩ := F.surjective c
  induction q using Quotient.inductionOn with | h f => ?_
  rw [map_pow, genusCharHom_apply_mk]
  obtain ⟨hfD, hfp⟩ := hS f f.property
  exact (hfD ▸ hχ).genusChar_sq (hfp.exists_isUnit_eval (NeZero.ne m))

end Transport

section Narrow

variable (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)] (hpos : 0 < D) [NeZero m]

/-- **The genus character on the narrow Picard group.** For nonsquare `D > 0`, a genus character
`χ` of discriminant `D` with nonzero modulus defines a homomorphism `NarrowPic 𝒪_D →* R`, the
value at the class of a primitive form `f` of discriminant `D` being `genusChar χ f`
(`narrowPicGenusChar_narrowPicClass`). -/
noncomputable def narrowPicGenusChar (hχ : IsGenusChar D χ) :
    NarrowPic (QuadraticOrder.numberFieldOrder D hD) →* R :=
  genusCharHom (fun f hf ↦ (mem_primitiveForms D f).mp hf) hχ (properClassEquivNarrowPic D hD hpos)
    ⟨principalForm D, principalForm_mem_primitiveForms hD⟩ rfl
    (by rw [properClassEquivNarrowPic_apply]; exact properClassToNarrowPic_principalForm D hD)
    fun q₁ q₂ ↦ by
      simpa only [properClassEquivNarrowPic_apply] using
        exists_properClassToNarrowPic_mul_properClassToNarrowPic_eq D hD q₁ q₂

/-- The genus character on `NarrowPic 𝒪_D` sends the narrow class of a primitive form `f` of
discriminant `D` to `genusChar χ f`. -/
@[simp]
theorem narrowPicGenusChar_narrowPicClass (hχ : IsGenusChar D χ) {f : BinaryQuadraticForm ℤ}
    (hf : f.discrim = D) (hprim : f.IsPrimitive) :
    narrowPicGenusChar D hD hpos hχ (f.narrowPicClass D hf hprim) = genusChar χ f := by
  have hmem : f ∈ primitiveForms D := (mem_primitiveForms D f).mpr ⟨hf, hprim⟩
  rw [← properClassToNarrowPic_mk D hD ⟨f, hmem⟩, ← properClassEquivNarrowPic_apply D hD hpos]
  exact genusCharHom_apply_mk _ hχ ⟨f, hmem⟩

/-- The genus character on `NarrowPic 𝒪_D` is trivial on squares. -/
theorem narrowPicGenusChar_sq (hχ : IsGenusChar D χ)
    (c : NarrowPic (QuadraticOrder.numberFieldOrder D hD)) :
    narrowPicGenusChar D hD hpos hχ (c ^ 2) = 1 :=
  genusCharHom_sq _ hχ c

end Narrow

section PosDef

variable (n : ℕ) [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) [NeZero m]

/-- **The genus character on the Picard group.** For `D = -n < 0`, a genus character `χ` of
discriminant `-n` with nonzero modulus defines a homomorphism `Pic 𝒪_{-n} →* R`, the value at the
class of a primitive positive definite form `f` of discriminant `-n` being `genusChar χ f`
(`picGenusChar_picClass`). -/
noncomputable def picGenusChar (hχ : IsGenusChar (-n) χ) :
    Pic (QuadraticOrder.numberFieldOrder (-n) hn) →* R :=
  genusCharHom (fun _ hf ↦ ⟨((mem_posDef_inf_primitiveForms n).mp hf).1,
      ((mem_posDef_inf_primitiveForms n).mp hf).2.2⟩) hχ (posDefProperClassEquivPic n hn)
    ⟨principalForm (-n), principalForm_mem_posDef_inf_primitiveForms n hn⟩ rfl
    ((posDefProperClassEquivPic_apply n hn _).trans (posDefProperClassToPic_principalForm n hn))
    fun q₁ q₂ ↦ by
      obtain ⟨a, a', B, C, f, g, h, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
        exists_posDefProperClassToPic_mul_posDefProperClassToPic_eq n hn q₁ q₂
      -- Unlike the narrow case, `simp`/`rw` with `posDefProperClassEquivPic_apply` cannot match
      -- here: the codomain of `posDefProperClassToPic` carries `-((n : ℤ) : ℚ)` rather than
      -- `((-n : ℤ) : ℚ)`, so the two `Pic` groups agree only up to unfolding `Int.cast_neg`. The
      -- identification therefore goes through this explicit chain, checked by definitional
      -- unfolding.
      exact ⟨a, a', B, C, f, g, h, h₁, h₂, h₃, h₄, h₅,
        (congrArg₂ (· * ·) (posDefProperClassEquivPic_apply n hn q₁)
          (posDefProperClassEquivPic_apply n hn q₂)).trans
          (h₆.trans (posDefProperClassEquivPic_apply n hn _).symm)⟩

/-- The genus character on `Pic 𝒪_{-n}` sends the Picard class of a primitive positive definite
form `f` of discriminant `-n` to `genusChar χ f`. -/
-- Not `@[simp]`: `Rat.intCast_neg` rewrites the field `ℚ(√(-n))` inside the type of the left-hand
-- side, so it is not in simp normal form.
theorem picGenusChar_picClass (hχ : IsGenusChar (-n) χ) {f : BinaryQuadraticForm ℤ}
    (hf : f ∈ primitiveForms (-n)) (ha : 0 < f.a) :
    picGenusChar n hn hχ (picClass (-n) hn ⟨f, hf⟩) = genusChar χ f := by
  have hmem : f ∈ posDef n ⊓ primitiveForms (-n) := (mem_posDef_inf_primitiveForms n).mpr
    ⟨((mem_primitiveForms _ f).mp hf).1, ha, ((mem_primitiveForms _ f).mp hf).2⟩
  rw [← posDefProperClassToPic_mk n hn ⟨f, hmem⟩, ← posDefProperClassEquivPic_apply n hn]
  exact genusCharHom_apply_mk _ hχ ⟨f, hmem⟩

/-- The genus character on `Pic 𝒪_{-n}` is trivial on squares. -/
theorem picGenusChar_sq (hχ : IsGenusChar (-n) χ)
    (c : Pic (QuadraticOrder.numberFieldOrder (-n) hn)) : picGenusChar n hn hχ (c ^ 2) = 1 :=
  genusCharHom_sq _ hχ c

end PosDef

end TauCeti.BinaryQuadraticForm
