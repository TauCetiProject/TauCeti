/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action
public import TauCeti.NumberTheory.ModularForms.Newforms.Basic

/-!
# Good Hecke eigenforms and newforms, as bundled forms

A **good Hecke eigenform** of level `Γ₁(N)` and weight `k` is a nonzero cusp form with a
nebentypus `χ` that is a simultaneous eigenvector of the `Γ₀(N)` Hecke ring acting on
`cuspFormCharSpace k χ` (`heckeRingHomCuspCharSpace`), at every index coprime to the level.
A **newform** is a good Hecke eigenform lying in the new subspace and normalised by `a₁ = 1`:
Miyake's *primitive form* (§4.6). Both are bundled here as structures extending `CuspForm`, so
that the character, the eigenvalue system and the analytic invariants travel with the form.

## Design

* Eigen-ness is demanded only at indices coprime to `N`, and the eigenvalues are stored only
  there: `eigenvalue n hn` takes the coprimality proof `hn` as an argument, and `isEigen n hn`
  is its characteristic equation, `heckeTCompositeGamma0 N n` acting on the form by
  `eigenvalue n hn`. No value and no eigencondition is packaged at an index not coprime to
  `N`; the ring element exists there, but its action on a good eigenform is not part of this
  notion (and is not a claim about `U_n`).
* A good eigenform is determined by its underlying cusp form: the character by
  `eq_of_mem_cuspFormCharSpace_of_ne_zero`, the eigenvalues by cancelling the nonzero form in
  the eigenvector equations (`EigenformAwayFromLevel.ext`).
* That a newform is an eigenvector of every `T_n` is a theorem (Atkin–Lehner–Li; Miyake
  Theorem 4.6.13), not a field, and so is the comparison of the ring eigenvalues with the
  classical operator `heckeTCuspNat`; neither is proved here.

## Main definitions

* `HeckeRing.GL2.EigenformAwayFromLevel`: the bundled good Hecke eigenform, with its
  eigenvalue system `EigenformAwayFromLevel.eigenvalue` at the indices coprime to the level.
* `HeckeRing.GL2.Newform`: the bundled newform.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.ext`, `HeckeRing.GL2.Newform.ext`: the bundled data is
  determined by the underlying cusp form.
* `HeckeRing.GL2.Newform.qExpansion_coeff_one`: the normalisation `a₁ = 1` as a simp lemma.

## Provenance

Follows the shapes of `structure Eigenform` and `structure Newform` of the AINTLIB
`LeanModularForms` project (`LeanModularForms/HeckeRIngs/GL2/Newforms/{Basic,MainLemma}.lean`,
Chris Birkbeck, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), with these
differences: the structure is named for the qualified notion, nonzeroness is a field, the
character space is the cusp-form one, and the eigenvalues are stored at the good indices only
rather than as a total function with unconstrained values at the bad ones. The source's
classical eigenvalue `Eigenform.eigenvalue` (which in its convention carries a diamond factor
`χ(n)`) is not reproduced.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn

open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **A good Hecke eigenform, bundled.** A nonzero cusp form of level `Γ₁(N)` with a nebentypus
`χ`, together with an eigenvalue system for the `Γ₀(N)` Hecke ring acting on
`cuspFormCharSpace k χ`: at every index `n` coprime to `N`, the ring element
`heckeTCompositeGamma0 N n` acts by the scalar `eigenvalue n hn`. Eigen-ness is demanded, and an
eigenvalue stored, only away from the level. -/
structure EigenformAwayFromLevel (N : ℕ) [NeZero N] (k : ℤ)
    extends CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  /-- The nebentypus character. -/
  χ : (ZMod N)ˣ →* ℂˣ
  /-- The form transforms under the diamond operators by `χ`. -/
  mem_charSpace : toCuspForm ∈ cuspFormCharSpace k χ
  /-- The eigenvalue at an index coprime to the level. -/
  eigenvalue : ∀ n : ℕ+, Nat.Coprime n.val N → ℂ
  /-- At an index `n` coprime to `N`, the Hecke ring element `heckeTCompositeGamma0 N n` acts on
  the form by `eigenvalue n hn`. -/
  isEigen : ∀ (n : ℕ+) (hn : Nat.Coprime n.val N),
    heckeRingHomCuspCharSpace (k := k) (χ := χ) (heckeTCompositeGamma0 N n.val)
        ⟨toCuspForm, mem_charSpace⟩
      = eigenvalue n hn • (⟨toCuspForm, mem_charSpace⟩ : cuspFormCharSpace k χ)
  /-- An eigenform is nonzero. -/
  ne_zero : toCuspForm ≠ 0

/-- **A newform**: a good Hecke eigenform lying in the new subspace and normalised by `a₁ = 1`
(Miyake's *primitive form*). That a newform is an eigenform for every `T_n` is a theorem, not
part of the definition. -/
structure Newform (N : ℕ) [NeZero N] (k : ℤ) extends EigenformAwayFromLevel N k where
  /-- The form lies in the new subspace `S_k(Γ₁(N))ⁿᵉʷ`. -/
  isNew : toCuspForm ∈ TauCeti.cuspFormsNew N k
  /-- The form is normalised: its first Fourier coefficient is `1`. -/
  isNorm : (qExpansion 1 toCuspForm).coeff 1 = 1

namespace EigenformAwayFromLevel

/-- **Extensionality**: two good Hecke eigenforms with the same underlying cusp form are equal.
The form determines its nebentypus, and the eigenvalues at good indices are read off the
eigenvector equations. -/
@[ext]
theorem ext {f g : EigenformAwayFromLevel N k} (h : f.toCuspForm = g.toCuspForm) : f = g := by
  obtain ⟨F, χf, memf, af, eigf, nzf⟩ := f
  obtain ⟨G, χg, memg, ag, eigg, nzg⟩ := g
  simp only at h
  subst h
  obtain rfl : χf = χg := eq_of_mem_cuspFormCharSpace_of_ne_zero memf memg nzf
  have hx : (⟨F, memf⟩ : cuspFormCharSpace k χf) ≠ 0 := fun hx ↦ nzf (congrArg Subtype.val hx)
  have hae : af = ag := funext fun n ↦ funext fun hn ↦
    smul_left_injective ℂ hx ((eigf n hn).symm.trans (eigg n hn))
  subst hae
  rfl

end EigenformAwayFromLevel

namespace Newform

/-- The normalisation `a₁ = 1`, as a simp lemma. The eigenvector equation `isEigen` has no simp
form: its right-hand side depends on the coprimality proof, so no rewrite rule can produce it. -/
@[simp]
theorem qExpansion_coeff_one (f : Newform N k) : (qExpansion 1 f.toCuspForm).coeff 1 = 1 :=
  f.isNorm

/-- **Extensionality**: two newforms with the same underlying cusp form are equal. -/
@[ext]
theorem ext {f g : Newform N k} (h : f.toCuspForm = g.toCuspForm) : f = g := by
  obtain ⟨f, hfn, hf1⟩ := f
  obtain ⟨g, hgn, hg1⟩ := g
  have : f = g := EigenformAwayFromLevel.ext h
  subst this
  rfl

end Newform

end HeckeRing.GL2
