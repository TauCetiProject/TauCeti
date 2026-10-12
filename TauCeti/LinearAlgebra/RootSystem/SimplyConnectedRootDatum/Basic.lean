/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Dual
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Scaffolding shared by the pinned simply connected root data

The pinned simply connected root data are integral root data, one per valid Dynkin type, each on
the lattices `Fin n → ℤ` with the dot product as pairing, and each carrying a base whose support is
the image of an injective *simple index* map `e` naming the simple roots in Bourbaki order. This
file holds the part of that construction which carries no information about the type: only the
per-type files, such as `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A` and
`...SimplyConnectedRootDatum.D.Basic`, supply the mathematics of their own root system.

## Main definitions

* `TauCeti.simpleSupport`: the support of a pinned base, the image of a simple index map.

## Main results

* `TauCeti.hasCartanType_of_pairing_eq`: a base supported on a simple index map has Cartan type `t`
  as soon as the pairings of the simple roots are the entries of the standard Cartan matrix of `t`.
* `TauCeti.corootSpan_eq_top_of_coroot_eq_single`: the coroots span the cocharacter lattice as soon
  as the simple coroots are the standard basis. This is the simply connected lattice condition.

The membership axioms of `RootPairing.Base` are met by the pinned data through
`TauCeti.sum_smul_mem_or_neg_mem_closure` in `TauCeti/Algebra/Group/Submonoid/Closure.lean`, or,
for data written in a coordinate potential, through `TauCeti.sub_mem_closure_of_le` in
`TauCeti/Algebra/Group/Submonoid/Telescoping.lean`. Every pinned datum pairs its two lattices by
the dot product, which is a perfect pairing by `TauCeti.dotProductBilin_isPerfPair` in
`TauCeti/LinearAlgebra/Matrix/Dual.lean`. The symmetry and reflection preservation of the quadratic
form carried by the Cartan matrix are supplied by `TauCeti.vecMul_dotProduct_comm` and
`TauCeti.reflect_vecMul_dotProduct_self` in `TauCeti/LinearAlgebra/Matrix/Gram.lean`.
-/

public section

namespace TauCeti

open Function Set

/-! ## The support of a pinned base -/

section SimpleSupport

variable {ι κ : Type*} [Fintype κ] {e : κ → ι} (he : Injective e)

/-- The support of a pinned base: the image of the simple index map `e`, which names the simple
roots among all root indices. -/
def simpleSupport : Finset ι :=
  Finset.univ.map ⟨e, he⟩

@[simp]
theorem mem_simpleSupport {k : ι} : k ∈ simpleSupport he ↔ ∃ i, e i = k := by
  simp [simpleSupport]

@[simp, norm_cast]
theorem coe_simpleSupport : (simpleSupport he : Set ι) = range e := by
  simp [simpleSupport]

/-- The image of a pinned support under a family indexed by the root indices is the range of the
family's restriction to the simple indices. -/
theorem image_simpleSupport {M : Type*} (f : ι → M) :
    f '' (simpleSupport he : Set ι) = range (f ∘ e) := by
  rw [coe_simpleSupport, range_comp]

/-- Linear independence of the simple members of a family is linear independence on the pinned
support, the form in which `RootPairing.Base` asks for it. -/
theorem linearIndepOn_simpleSupport {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : ι → M) (h : LinearIndependent R (f ∘ e)) : LinearIndepOn R f (simpleSupport he) := by
  rw [coe_simpleSupport]
  exact (linearIndepOn_range_iff he f).mpr h

end SimpleSupport

section SimpleSupportFin

variable {n N : ℕ} {e : Fin n → Fin N}

/-- **A pinned support numbered in order is an initial segment.** When the simple index map sends
`i` to the root index `i`, membership in the support is the bound `k < n` on the index. -/
theorem mem_simpleSupport_iff_lt (he : Injective e) (h : ∀ i, (e i : ℕ) = i)
    {k : Fin N} : k ∈ simpleSupport he ↔ (k : ℕ) < n := by
  rw [mem_simpleSupport]
  refine ⟨?_, fun hk => ⟨⟨k, hk⟩, Fin.ext (h ⟨k, hk⟩)⟩⟩
  rintro ⟨i, rfl⟩
  rw [h i]
  exact i.isLt

end SimpleSupportFin

/-! ## Recognizing the pinned data -/

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **A pinned base has the Cartan type its simple pairings display.** The Cartan matrix of a base
supported on a simple index map is read off the pairings of the simple roots, so a base whose
simple pairings are the entries of the standard Cartan matrix of `t` has Cartan type `t`. -/
theorem hasCartanType_of_pairing_eq [FaithfulSMul ℤ R] {P : RootPairing ι R M N}
    [P.IsCrystallographic] {b : P.Base} {t : DynkinType} {e : Fin t.rank → ι} (he : Injective e)
    (hb : b.support = simpleSupport he)
    (h : ∀ i j, P.pairing (e i) (e j) = algebraMap ℤ R (t.cartanMatrix i j)) :
    HasCartanType P b t := by
  let r : b.support ≃ range e := Equiv.subtypeEquivRight fun k => by simp [hb]
  let q : b.support ≃ Fin t.rank := r.trans (Equiv.ofInjective e he).symm
  have hval (x : b.support) : (x : ι) = e (q x) := (Equiv.apply_ofInjective_symm he (r x)).symm
  refine (hasCartanType_iff b t).mpr ⟨q, fun i j => ?_⟩
  rw [← (FaithfulSMul.algebraMap_injective ℤ R).eq_iff,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply, hval i, hval j, h]

/-- **The coroots span the cocharacter lattice when the simple coroots are the standard basis.**
For a root datum on the lattice `κ → ℤ` this is the simply connected lattice condition. -/
theorem corootSpan_eq_top_of_coroot_eq_single {κ : Type*} [Finite κ] [DecidableEq κ]
    {P : RootPairing ι R M (κ → R)} {e : κ → ι} (h : ∀ i, P.coroot (e i) = Pi.single i 1) :
    P.corootSpan R = ⊤ := by
  refine top_unique ?_
  rw [← (Pi.basisFun R κ).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨e i, by rw [h i]; simp⟩

end RootPairing

end TauCeti
