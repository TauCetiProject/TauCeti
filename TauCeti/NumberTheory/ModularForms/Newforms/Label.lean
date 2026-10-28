/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.GaloisOrbitLabel
public import TauCeti.NumberTheory.ModularForms.Newforms.Conjugate

/-!
# The prefix `N.k.a` of the LMFDB label of a newform

The LMFDB labels a newform `f` of level `N`, weight `k` and nebentypus `χ` by `N.k.a.x`. The
prefix `N.k.a` names the newspace `S_k^new(N, [χ])` spanned by the newforms of level `N` and
weight `k` whose nebentypus lies in the Galois orbit `[χ]`: the component `a` is the label of the
Galois orbit of `χ` among the Galois orbits of Dirichlet characters modulo `N`
(`DirichletCharacter.galoisOrbitIndex`). The last component `x` labels the Galois orbit of `f`
inside this newspace.

We record the prefix as a `TauCeti.NewformLabelPrefix`, with the character component as its
index `0, 1, 2, …`, which the LMFDB writes in base `26` with the digits `a, …, z`. Two newforms
of the same level have the same prefix exactly when they have the same weight and Galois
conjugate nebentypus (`HeckeRing.GL2.Newform.labelPrefix_eq_labelPrefix_iff`). In particular the
conjugate newform `f_ρ`, of nebentypus `χ⁻¹`, has the same prefix as `f`, and the prefix of a
newform ends in `a` exactly when its nebentypus is trivial.

## Main definitions

* `TauCeti.NewformLabelPrefix`: the triple `N.k.a` of a level, a weight and the index of a
  Galois orbit of Dirichlet characters.
* `HeckeRing.GL2.Newform.labelPrefix f`: the prefix `N.k.a` of the label of the newform `f`.

## Main results

* `HeckeRing.GL2.Newform.labelPrefix_eq_labelPrefix_iff`: two newforms of the same level have the
  same prefix exactly when they have the same weight and Galois conjugate nebentypus.
* `HeckeRing.GL2.Newform.labelPrefix_conj`: the conjugate newform has the same prefix.
* `HeckeRing.GL2.Newform.charOrbit_labelPrefix_eq_zero_iff`: the character component is `a`
  exactly for trivial nebentypus.

## References

* The LMFDB Collaboration, *Labels for classical modular forms*,
  <https://www.lmfdb.org/knowledge/show/cmf.label>.
* J. Best, J. Bober, A. R. Booker, E. Costa, J. E. Cremona, M. Derickx, M. Lee, D. Lowry-Duda,
  D. Roe, A. V. Sutherland, J. Voight, *Computing classical modular forms*.
-/

public section

namespace TauCeti

/-- The prefix `N.k.a` of the LMFDB label `N.k.a.x` of a classical newform: a level `N`, a weight
`k`, and the index `a` of a Galois orbit of Dirichlet characters modulo `N` in the LMFDB order
(`DirichletCharacter.galoisOrbitIndex`). It names a newspace `S_k^new(N, [χ])`. -/
@[ext]
structure NewformLabelPrefix where
  /-- The level `N`. -/
  level : ℕ
  /-- The weight `k`. -/
  weight : ℤ
  /-- The index of the Galois orbit of the nebentypus among the Galois orbits of Dirichlet
  characters modulo the level, written by the LMFDB in base `26` with the digits `a, …, z`. -/
  charOrbit : ℕ

end TauCeti

namespace HeckeRing.GL2.Newform

open TauCeti

variable {N : ℕ} [NeZero N] {k l : ℤ}

/-- **The prefix `N.k.a` of the LMFDB label** of a newform `f` of level `N`, weight `k` and
nebentypus `χ`: the level, the weight, and the index of the Galois orbit of `χ` among the Galois
orbits of Dirichlet characters modulo `N`. -/
noncomputable def labelPrefix (f : Newform N k) : NewformLabelPrefix where
  level := N
  weight := k
  charOrbit := f.dirichletLift.galoisOrbitIndex

/-- The level component of the label prefix. -/
@[simp]
theorem labelPrefix_level (f : Newform N k) : f.labelPrefix.level = N := (rfl)

/-- The weight component of the label prefix. -/
@[simp]
theorem labelPrefix_weight (f : Newform N k) : f.labelPrefix.weight = k := (rfl)

/-- The character component of the label prefix is the index of the Galois orbit of the
nebentypus. -/
@[simp]
theorem labelPrefix_charOrbit (f : Newform N k) :
    f.labelPrefix.charOrbit = f.dirichletLift.galoisOrbitIndex := (rfl)

/-- **Two newforms of the same level have the same label prefix exactly when they have the same
weight and Galois conjugate nebentypus.** -/
theorem labelPrefix_eq_labelPrefix_iff {f : Newform N k} {g : Newform N l} :
    g.labelPrefix = f.labelPrefix ↔ l = k ∧ g.dirichletLift ∈ f.dirichletLift.galoisOrbit := by
  simp [NewformLabelPrefix.ext_iff, DirichletCharacter.galoisOrbitIndex_eq_galoisOrbitIndex_iff]

/-- The Dirichlet character of the conjugate newform is the inverse of that of the newform. -/
theorem dirichletLift_conj (f : Newform N k) : f.conj.dirichletLift = f.dirichletLift⁻¹ :=
  MulChar.ext fun u ↦ by
    simp [dirichletLift_def, χ_conj, MulChar.inv_apply_eq_inv']

/-- **The conjugate newform `f_ρ` has the same label prefix as `f`**: its nebentypus `χ⁻¹` is
Galois conjugate to `χ`. -/
@[simp]
theorem labelPrefix_conj (f : Newform N k) : f.conj.labelPrefix = f.labelPrefix :=
  labelPrefix_eq_labelPrefix_iff.mpr
    ⟨rfl, dirichletLift_conj f ▸ MulChar.inv_mem_galoisOrbit f.dirichletLift⟩

/-- The character component of the label prefix of a newform is `a`, the index `0`, exactly when
its nebentypus is trivial. -/
theorem charOrbit_labelPrefix_eq_zero_iff {f : Newform N k} :
    f.labelPrefix.charOrbit = 0 ↔ f.χ = 1 := by
  rw [labelPrefix_charOrbit, DirichletCharacter.galoisOrbitIndex_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ MulChar.ext fun u ↦ by simp [dirichletLift_def, h]⟩
  rw [← dirichletLift_equivToUnitHom, h]
  ext u
  simp

end HeckeRing.GL2.Newform
