/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.Algebra.Homology.SquareZero

/-!
# Linear homotopy equivalences of modules with a differential

`LinearHomotopyEquiv dM dN` packages a symmetric chain-homotopy equivalence between modules
`(M, dM)` and `(N, dN)` equipped with linear endomorphisms: two endomorphism-intertwining maps
`hom : M →ₗ[R] N` and `inv : N →ₗ[R] M` together with homotopies `homotopyHom : M →ₗ[R] M` and
`homotopyInv : N →ₗ[R] N` satisfying

`dM hM + hM dM = 1 - inv ∘ hom`,   `dN hN + hN dN = 1 - hom ∘ inv`.

Unlike `LinearContraction`, neither composite `hom ∘ inv` nor `inv ∘ hom` is required to be the
identity; every `LinearContraction` gives a `LinearHomotopyEquiv` with `homotopyInv = 0`
(`LinearContraction.toLinearHomotopyEquiv`).  Like `LinearContraction`, no square-zero hypothesis or
grading is built into the structure: homogeneity is tracked separately through
`TauCeti.LinearMap.IsHomogeneous`, and when `dM` and `dN` square to zero over a ring, a linear
homotopy equivalence induces a linear equivalence on homology
(`LinearHomotopyEquiv.homologyEquiv`).

## Adjoint normalization and coupled Hom-complex equations

Given an arbitrary homotopy equivalence `(f, g, hM, hN)`, the two homotopies need not be compatible
with `f`: the defect `δ = f hM - hN f` is a chain map (`dN δ + δ dM = 0`), not necessarily zero or
null-homotopic.  Vogt's adjoint promotion replaces `hN` by

`hN' = hN + (f hM - hN f) g`,

which still satisfies `dN hN' + hN' dN = 1 - f g`, while the new defect `f hM - hN' f` becomes the
chain boundary `dN m - m dM` of the second-order homotopy `m = -(f hM - hN f) hM`
(`LinearHomotopyEquiv.hom_comp_homotopyHom_sub_adjointHomotopyInv_comp_hom`).  No square-zero
assumption on `dM` or `dN` is needed for either identity.

This coherence makes `(f, g, hM, hN')` solve coupled obstruction problems in `Hom(P, -)` for any
module `(P, dP)` with an endomorphism: whenever `u : P →ₗ[R] M` satisfies `dM u = s • (u dP)` for
a sign `s : ℤˣ` and `v : P →ₗ[R] N` bounds `f u` via `dN v + s • (v dP) = f u`, the explicit maps
`x = g v + hM u` (`coupledLift`) and `z = hN' v - m u` (`coupledHomotopy`) simultaneously solve

`dM x + s • (x dP) = u`,   `v - f x = dN z - s • (z dP)`.

This single linear-algebraic step drives both the recursive construction of `A∞` homotopy inverses
and the acyclicity of postcomposition by an `A∞` morphism with homotopy-invertible linear part.

## Main definitions

* `TauCeti.LinearHomotopyEquiv`: a chain-homotopy equivalence between `(M, dM)` and `(N, dN)`.
* `TauCeti.LinearHomotopyEquiv.refl`, `symm`, `trans`: identity, symmetry and composition of linear
  homotopy equivalences.
* `TauCeti.LinearContraction.toLinearHomotopyEquiv`: view a contraction as a homotopy equivalence.
* `TauCeti.LinearHomotopyEquiv.homologyEquiv`: the linear equivalence on `ker d ⧸ im d` induced when
  `dM` and `dN` square to zero.
* `TauCeti.LinearHomotopyEquiv.adjointNormalize`: replace `homotopyInv` by `adjointHomotopyInv` so
  that `hom ∘ homotopyHom - adjointHomotopyInv ∘ hom` is bounded by `coherentHomotopy`.
* `TauCeti.LinearHomotopyEquiv.coupledLift` and `coupledHomotopy`: explicit solutions of coupled
  Hom-complex equations along a linear homotopy equivalence.

## References

* R. M. Vogt, *A note on homotopy equivalences*, Proc. Amer. Math. Soc. 32 (1972), 627--629.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Chapitre 1, Théorème 1.3.1.2.
-/

public section

universe uR uM uN uP

namespace TauCeti

section Semiring

variable {R : Type uR} {M : Type uM} {N : Type uN} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear homotopy equivalence between modules `(M, dM)` and `(N, dN)` with endomorphisms.
For square-zero endomorphisms this is a chain-homotopy equivalence of differential modules. -/
@[ext]
structure LinearHomotopyEquiv (dM : Module.End R M) (dN : Module.End R N) where
  /-- The forward chain map. -/
  hom : M →ₗ[R] N
  /-- The homotopy-inverse chain map. -/
  inv : N →ₗ[R] M
  /-- The homotopy between `1` and `inv ∘ hom` on `M`. -/
  homotopyHom : Module.End R M
  /-- The homotopy between `1` and `hom ∘ inv` on `N`. -/
  homotopyInv : Module.End R N
  /-- The forward map intertwines the endomorphisms. -/
  dN_comp_hom : dN ∘ₗ hom = hom ∘ₗ dM
  /-- The inverse map intertwines the endomorphisms. -/
  dM_comp_inv : dM ∘ₗ inv = inv ∘ₗ dN
  /-- The homotopy `homotopyHom` contracts `1 - inv ∘ hom`. -/
  dM_comp_homotopyHom_add_homotopyHom_comp_dM :
    dM ∘ₗ homotopyHom + homotopyHom ∘ₗ dM = LinearMap.id - inv ∘ₗ hom
  /-- The homotopy `homotopyInv` contracts `1 - hom ∘ inv`. -/
  dN_comp_homotopyInv_add_homotopyInv_comp_dN :
    dN ∘ₗ homotopyInv + homotopyInv ∘ₗ dN = LinearMap.id - hom ∘ₗ inv

namespace LinearHomotopyEquiv

attribute [simp] dN_comp_hom dM_comp_inv

section Basic

variable {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN)
  {P : Type uP} [AddCommGroup P] [Module R P]

/-- Reversed intertwining identity `hom ∘ dM = dN ∘ hom`, matching the orientation of
`LinearMap.homologyMap`. -/
theorem hom_comp_dM : e.hom ∘ₗ dM = dN ∘ₗ e.hom :=
  e.dN_comp_hom.symm

/-- Reversed intertwining identity `inv ∘ dN = dM ∘ inv`, matching the orientation of
`LinearMap.homologyMap`. -/
theorem inv_comp_dN : e.inv ∘ₗ dN = dM ∘ₗ e.inv :=
  e.dM_comp_inv.symm

@[simp]
theorem dN_comp_hom_assoc (f : P →ₗ[R] M) : dN ∘ₗ e.hom ∘ₗ f = e.hom ∘ₗ dM ∘ₗ f := by
  rw [← LinearMap.comp_assoc, e.dN_comp_hom, LinearMap.comp_assoc]

@[simp]
theorem dM_comp_inv_assoc (f : P →ₗ[R] N) : dM ∘ₗ e.inv ∘ₗ f = e.inv ∘ₗ dN ∘ₗ f := by
  rw [← LinearMap.comp_assoc, e.dM_comp_inv, LinearMap.comp_assoc]

@[simp]
theorem dN_hom_apply (x : M) : dN (e.hom x) = e.hom (dM x) :=
  LinearMap.congr_fun e.dN_comp_hom x

@[simp]
theorem dM_inv_apply (y : N) : dM (e.inv y) = e.inv (dN y) :=
  LinearMap.congr_fun e.dM_comp_inv y

theorem inv_comp_hom : e.inv ∘ₗ e.hom =
    LinearMap.id - (dM ∘ₗ e.homotopyHom + e.homotopyHom ∘ₗ dM) := by
  rw [e.dM_comp_homotopyHom_add_homotopyHom_comp_dM, sub_sub_cancel]

theorem hom_comp_inv : e.hom ∘ₗ e.inv =
    LinearMap.id - (dN ∘ₗ e.homotopyInv + e.homotopyInv ∘ₗ dN) := by
  rw [e.dN_comp_homotopyInv_add_homotopyInv_comp_dN, sub_sub_cancel]

variable (dM) in
/-- The identity homotopy equivalence on `(M, dM)`, with zero homotopies. -/
def refl : LinearHomotopyEquiv dM dM where
  hom := LinearMap.id
  inv := LinearMap.id
  homotopyHom := 0
  homotopyInv := 0
  dN_comp_hom := by rw [LinearMap.comp_id, LinearMap.id_comp]
  dM_comp_inv := by rw [LinearMap.comp_id, LinearMap.id_comp]
  dM_comp_homotopyHom_add_homotopyHom_comp_dM := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp, add_zero, LinearMap.id_comp, sub_self]
  dN_comp_homotopyInv_add_homotopyInv_comp_dN := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp, add_zero, LinearMap.id_comp, sub_self]

@[simp] theorem refl_hom : (refl dM).hom = LinearMap.id := (rfl)
@[simp] theorem refl_inv : (refl dM).inv = LinearMap.id := (rfl)
@[simp] theorem refl_homotopyHom : (refl dM).homotopyHom = 0 := (rfl)
@[simp] theorem refl_homotopyInv : (refl dM).homotopyInv = 0 := (rfl)

/-- Reverse a linear homotopy equivalence by swapping `hom` with `inv` and `homotopyHom` with
`homotopyInv`. -/
@[symm]
def symm : LinearHomotopyEquiv dN dM where
  hom := e.inv
  inv := e.hom
  homotopyHom := e.homotopyInv
  homotopyInv := e.homotopyHom
  dN_comp_hom := e.dM_comp_inv
  dM_comp_inv := e.dN_comp_hom
  dM_comp_homotopyHom_add_homotopyHom_comp_dM := e.dN_comp_homotopyInv_add_homotopyInv_comp_dN
  dN_comp_homotopyInv_add_homotopyInv_comp_dN := e.dM_comp_homotopyHom_add_homotopyHom_comp_dM

@[simp] theorem symm_hom : e.symm.hom = e.inv := (rfl)
@[simp] theorem symm_inv : e.symm.inv = e.hom := (rfl)
@[simp] theorem symm_homotopyHom : e.symm.homotopyHom = e.homotopyInv := (rfl)
@[simp] theorem symm_homotopyInv : e.symm.homotopyInv = e.homotopyHom := (rfl)
@[simp] theorem symm_symm : e.symm.symm = e := (rfl)

/-- Compose two linear homotopy equivalences. -/
@[trans]
def trans {dP : Module.End R P} (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
    LinearHomotopyEquiv dM dP where
  hom := e₂.hom ∘ₗ e₁.hom
  inv := e₁.inv ∘ₗ e₂.inv
  homotopyHom := e₁.homotopyHom + e₁.inv ∘ₗ e₂.homotopyHom ∘ₗ e₁.hom
  homotopyInv := e₂.homotopyInv + e₂.hom ∘ₗ e₁.homotopyInv ∘ₗ e₂.inv
  dN_comp_hom := by rw [e₂.dN_comp_hom_assoc, e₁.dN_comp_hom, LinearMap.comp_assoc]
  dM_comp_inv := by rw [e₁.dM_comp_inv_assoc, e₂.dM_comp_inv, LinearMap.comp_assoc]
  dM_comp_homotopyHom_add_homotopyHom_comp_dM := by
    calc
      dM ∘ₗ (e₁.homotopyHom + e₁.inv ∘ₗ e₂.homotopyHom ∘ₗ e₁.hom) +
          (e₁.homotopyHom + e₁.inv ∘ₗ e₂.homotopyHom ∘ₗ e₁.hom) ∘ₗ dM
        = (dM ∘ₗ e₁.homotopyHom + e₁.homotopyHom ∘ₗ dM) +
            e₁.inv ∘ₗ (dN ∘ₗ e₂.homotopyHom + e₂.homotopyHom ∘ₗ dN) ∘ₗ e₁.hom := by
          simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_assoc,
            e₁.dM_comp_inv_assoc, ← e₁.dN_comp_hom]
          abel
      _ = (LinearMap.id - e₁.inv ∘ₗ e₁.hom) +
            e₁.inv ∘ₗ (LinearMap.id - e₂.inv ∘ₗ e₂.hom) ∘ₗ e₁.hom := by
          rw [e₁.dM_comp_homotopyHom_add_homotopyHom_comp_dM,
            e₂.dM_comp_homotopyHom_add_homotopyHom_comp_dM]
      _ = LinearMap.id - (e₁.inv ∘ₗ e₂.inv) ∘ₗ (e₂.hom ∘ₗ e₁.hom) := by
          simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
            LinearMap.comp_assoc]
          abel
  dN_comp_homotopyInv_add_homotopyInv_comp_dN := by
    calc
      dP ∘ₗ (e₂.homotopyInv + e₂.hom ∘ₗ e₁.homotopyInv ∘ₗ e₂.inv) +
          (e₂.homotopyInv + e₂.hom ∘ₗ e₁.homotopyInv ∘ₗ e₂.inv) ∘ₗ dP
        = (dP ∘ₗ e₂.homotopyInv + e₂.homotopyInv ∘ₗ dP) +
            e₂.hom ∘ₗ (dN ∘ₗ e₁.homotopyInv + e₁.homotopyInv ∘ₗ dN) ∘ₗ e₂.inv := by
          simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_assoc,
            e₂.dN_comp_hom_assoc, ← e₂.dM_comp_inv]
          abel
      _ = (LinearMap.id - e₂.hom ∘ₗ e₂.inv) +
            e₂.hom ∘ₗ (LinearMap.id - e₁.hom ∘ₗ e₁.inv) ∘ₗ e₂.inv := by
          rw [e₂.dN_comp_homotopyInv_add_homotopyInv_comp_dN,
            e₁.dN_comp_homotopyInv_add_homotopyInv_comp_dN]
      _ = LinearMap.id - (e₂.hom ∘ₗ e₁.hom) ∘ₗ (e₁.inv ∘ₗ e₂.inv) := by
          simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
            LinearMap.comp_assoc]
          abel

@[simp]
theorem trans_hom {dP : Module.End R P} (e₁ : LinearHomotopyEquiv dM dN)
    (e₂ : LinearHomotopyEquiv dN dP) : (e₁.trans e₂).hom = e₂.hom ∘ₗ e₁.hom :=
  (rfl)

@[simp]
theorem trans_inv {dP : Module.End R P} (e₁ : LinearHomotopyEquiv dM dN)
    (e₂ : LinearHomotopyEquiv dN dP) : (e₁.trans e₂).inv = e₁.inv ∘ₗ e₂.inv :=
  (rfl)

@[simp]
theorem trans_homotopyHom {dP : Module.End R P} (e₁ : LinearHomotopyEquiv dM dN)
    (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).homotopyHom = e₁.homotopyHom + e₁.inv ∘ₗ e₂.homotopyHom ∘ₗ e₁.hom :=
  (rfl)

@[simp]
theorem trans_homotopyInv {dP : Module.End R P} (e₁ : LinearHomotopyEquiv dM dN)
    (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).homotopyInv = e₂.homotopyInv + e₂.hom ∘ₗ e₁.homotopyInv ∘ₗ e₂.inv :=
  (rfl)

/-- Composing degree-zero homotopy equivalences preserves homotopy degree `q`. -/
theorem isHomogeneous_trans_homotopyHom {dP : Module.End R P} {e₁ : LinearHomotopyEquiv dM dN}
    {e₂ : LinearHomotopyEquiv dN dP} {ι σM σN : Type*} [AddMonoid ι]
    [SetLike σM M] [AddMemClass σM M] [SetLike σN N] {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι}
    (hf₁ : LinearMap.IsHomogeneous e₁.hom 𝒜 ℬ 0) (hg₁ : LinearMap.IsHomogeneous e₁.inv ℬ 𝒜 0)
    (hh₁ : LinearMap.IsHomogeneous e₁.homotopyHom 𝒜 𝒜 q)
    (hh₂ : LinearMap.IsHomogeneous e₂.homotopyHom ℬ ℬ q) :
    LinearMap.IsHomogeneous (e₁.trans e₂).homotopyHom 𝒜 𝒜 q := by
  rw [trans_homotopyHom]
  exact hh₁.add (by simpa only [zero_add, add_zero] using hg₁.comp (hh₂.comp hf₁))

/-- Composing degree-zero homotopy equivalences preserves inverse homotopy degree `q`. -/
theorem isHomogeneous_trans_homotopyInv {dP : Module.End R P} {e₁ : LinearHomotopyEquiv dM dN}
    {e₂ : LinearHomotopyEquiv dN dP} {ι σN σP : Type*} [AddMonoid ι]
    [SetLike σN N] [SetLike σP P] [AddMemClass σP P] {ℬ : ι → σN} {𝒞 : ι → σP} {q : ι}
    (hf₂ : LinearMap.IsHomogeneous e₂.hom ℬ 𝒞 0) (hg₂ : LinearMap.IsHomogeneous e₂.inv 𝒞 ℬ 0)
    (hh₁ : LinearMap.IsHomogeneous e₁.homotopyInv ℬ ℬ q)
    (hh₂ : LinearMap.IsHomogeneous e₂.homotopyInv 𝒞 𝒞 q) :
    LinearMap.IsHomogeneous (e₁.trans e₂).homotopyInv 𝒞 𝒞 q := by
  rw [trans_homotopyInv]
  exact hh₂.add (by simpa only [zero_add, add_zero] using hf₂.comp (hh₁.comp hg₂))

end Basic

/-! ### Vogt's adjoint normalization -/

section Adjoint

variable {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN)

/-- The failure `f ∘ hM - hN ∘ f` of the two homotopies of `e` to commute with `hom`. -/
private def homotopyDefect : M →ₗ[R] N :=
  e.hom ∘ₗ e.homotopyHom - e.homotopyInv ∘ₗ e.hom

private theorem dN_comp_homotopyDefect_add_homotopyDefect_comp_dM :
    dN ∘ₗ e.homotopyDefect + e.homotopyDefect ∘ₗ dM = 0 := by
  calc
    dN ∘ₗ (e.hom ∘ₗ e.homotopyHom - e.homotopyInv ∘ₗ e.hom) +
        (e.hom ∘ₗ e.homotopyHom - e.homotopyInv ∘ₗ e.hom) ∘ₗ dM
      = e.hom ∘ₗ (dM ∘ₗ e.homotopyHom + e.homotopyHom ∘ₗ dM) -
          (dN ∘ₗ e.homotopyInv + e.homotopyInv ∘ₗ dN) ∘ₗ e.hom := by
        simp only [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_add, LinearMap.add_comp,
          LinearMap.comp_assoc, e.dN_comp_hom_assoc, ← e.dN_comp_hom]
        abel
    _ = e.hom ∘ₗ (LinearMap.id - e.inv ∘ₗ e.hom) -
          (LinearMap.id - e.hom ∘ₗ e.inv) ∘ₗ e.hom := by
        rw [e.dM_comp_homotopyHom_add_homotopyHom_comp_dM,
          e.dN_comp_homotopyInv_add_homotopyInv_comp_dN]
    _ = 0 := by
        simp only [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id, LinearMap.id_comp,
          LinearMap.comp_assoc, sub_self]

/-- Vogt's modified homotopy `hN + (f ∘ hM - hN ∘ f) ∘ g` on `N`.  It still contracts
`1 - f ∘ g`, and makes `f ∘ hM - hN' ∘ f` null-homotopic via `coherentHomotopy`. -/
def adjointHomotopyInv : Module.End R N :=
  e.homotopyInv + (e.hom ∘ₗ e.homotopyHom - e.homotopyInv ∘ₗ e.hom) ∘ₗ e.inv

theorem adjointHomotopyInv_def :
    e.adjointHomotopyInv =
      e.homotopyInv + (e.hom ∘ₗ e.homotopyHom - e.homotopyInv ∘ₗ e.hom) ∘ₗ e.inv :=
  (rfl)

/-- The second-order homotopy `-(f ∘ hM - hN ∘ f) ∘ hM` bounding
`f ∘ hM - adjointHomotopyInv ∘ f`. -/
def coherentHomotopy : M →ₗ[R] N :=
  -((e.hom ∘ₗ e.homotopyHom - e.homotopyInv ∘ₗ e.hom) ∘ₗ e.homotopyHom)

theorem coherentHomotopy_def :
    e.coherentHomotopy =
      -((e.hom ∘ₗ e.homotopyHom - e.homotopyInv ∘ₗ e.hom) ∘ₗ e.homotopyHom) :=
  (rfl)

/-- Vogt's modified homotopy `adjointHomotopyInv` still contracts `1 - hom ∘ inv`. -/
theorem dN_comp_adjointHomotopyInv_add_adjointHomotopyInv_comp_dN :
    dN ∘ₗ e.adjointHomotopyInv + e.adjointHomotopyInv ∘ₗ dN = LinearMap.id - e.hom ∘ₗ e.inv := by
  have hδ : dN ∘ₗ (e.homotopyDefect ∘ₗ e.inv) + (e.homotopyDefect ∘ₗ e.inv) ∘ₗ dN = 0 := by
    calc
      dN ∘ₗ (e.homotopyDefect ∘ₗ e.inv) + (e.homotopyDefect ∘ₗ e.inv) ∘ₗ dN
        = (dN ∘ₗ e.homotopyDefect + e.homotopyDefect ∘ₗ dM) ∘ₗ e.inv := by
          simp only [LinearMap.add_comp, LinearMap.comp_assoc, e.dM_comp_inv]
      _ = 0 := by rw [e.dN_comp_homotopyDefect_add_homotopyDefect_comp_dM, LinearMap.zero_comp]
  calc
    dN ∘ₗ e.adjointHomotopyInv + e.adjointHomotopyInv ∘ₗ dN
      = (dN ∘ₗ e.homotopyInv + e.homotopyInv ∘ₗ dN) +
          (dN ∘ₗ (e.homotopyDefect ∘ₗ e.inv) + (e.homotopyDefect ∘ₗ e.inv) ∘ₗ dN) := by
        simp only [adjointHomotopyInv, homotopyDefect, LinearMap.comp_add, LinearMap.add_comp]
        abel
    _ = LinearMap.id - e.hom ∘ₗ e.inv := by
        rw [hδ, add_zero, e.dN_comp_homotopyInv_add_homotopyInv_comp_dN]

/-- Promote a linear homotopy equivalence to an adjoint homotopy equivalence by replacing
`homotopyInv` with `adjointHomotopyInv`. -/
def adjointNormalize : LinearHomotopyEquiv dM dN where
  hom := e.hom
  inv := e.inv
  homotopyHom := e.homotopyHom
  homotopyInv := e.adjointHomotopyInv
  dN_comp_hom := e.dN_comp_hom
  dM_comp_inv := e.dM_comp_inv
  dM_comp_homotopyHom_add_homotopyHom_comp_dM := e.dM_comp_homotopyHom_add_homotopyHom_comp_dM
  dN_comp_homotopyInv_add_homotopyInv_comp_dN :=
    e.dN_comp_adjointHomotopyInv_add_adjointHomotopyInv_comp_dN

@[simp] theorem adjointNormalize_hom : e.adjointNormalize.hom = e.hom := (rfl)
@[simp] theorem adjointNormalize_inv : e.adjointNormalize.inv = e.inv := (rfl)
@[simp] theorem adjointNormalize_homotopyHom :
    e.adjointNormalize.homotopyHom = e.homotopyHom := (rfl)
@[simp] theorem adjointNormalize_homotopyInv :
    e.adjointNormalize.homotopyInv = e.adjointHomotopyInv := (rfl)

/-- Coherence identity of Vogt's adjoint normalization: the defect between `homotopyHom` and
`adjointHomotopyInv` across `hom` is bounded by `coherentHomotopy`. -/
theorem hom_comp_homotopyHom_sub_adjointHomotopyInv_comp_hom :
    e.hom ∘ₗ e.homotopyHom - e.adjointHomotopyInv ∘ₗ e.hom =
      dN ∘ₗ e.coherentHomotopy - e.coherentHomotopy ∘ₗ dM := by
  have hδ : e.homotopyDefect ∘ₗ dM = -(dN ∘ₗ e.homotopyDefect) :=
    eq_neg_of_add_eq_zero_right e.dN_comp_homotopyDefect_add_homotopyDefect_comp_dM
  calc
    e.hom ∘ₗ e.homotopyHom - e.adjointHomotopyInv ∘ₗ e.hom
      = e.homotopyDefect ∘ₗ (LinearMap.id - e.inv ∘ₗ e.hom) := by
        simp only [adjointHomotopyInv, homotopyDefect, LinearMap.add_comp, LinearMap.comp_sub,
          LinearMap.comp_id, LinearMap.comp_assoc]
        abel
    _ = (e.homotopyDefect ∘ₗ dM) ∘ₗ e.homotopyHom +
          e.homotopyDefect ∘ₗ e.homotopyHom ∘ₗ dM := by
        rw [← e.dM_comp_homotopyHom_add_homotopyHom_comp_dM, LinearMap.comp_add,
          ← LinearMap.comp_assoc]
    _ = dN ∘ₗ e.coherentHomotopy - e.coherentHomotopy ∘ₗ dM := by
        rw [hδ, coherentHomotopy, ← homotopyDefect, LinearMap.neg_comp, LinearMap.comp_neg,
          LinearMap.neg_comp, LinearMap.comp_assoc]
        abel

/-- Adjoint normalization preserves homotopy degree `q` when `hom` and `inv` have degree zero. -/
theorem isHomogeneous_adjointHomotopyInv {ι σM σN : Type*} [AddMonoid ι]
    [SetLike σM M] [SetLike σN N] [AddMemClass σN N] [NegMemClass σN N]
    {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι}
    (hf : LinearMap.IsHomogeneous e.hom 𝒜 ℬ 0)
    (hg : LinearMap.IsHomogeneous e.inv ℬ 𝒜 0)
    (hhM : LinearMap.IsHomogeneous e.homotopyHom 𝒜 𝒜 q)
    (hhN : LinearMap.IsHomogeneous e.homotopyInv ℬ ℬ q) :
    LinearMap.IsHomogeneous e.adjointHomotopyInv ℬ ℬ q := by
  rw [adjointHomotopyInv_def]
  have hδ : LinearMap.IsHomogeneous (e.hom ∘ₗ e.homotopyHom - e.homotopyInv ∘ₗ e.hom) 𝒜 ℬ q :=
    LinearMap.IsHomogeneous.sub (by simpa only [add_zero] using hf.comp hhM)
      (by simpa only [zero_add] using hhN.comp hf)
  exact hhN.add (by simpa only [zero_add] using hδ.comp hg)

/-- When `hom` has degree zero and both homotopies have degree `q`, the second-order homotopy
`coherentHomotopy` has degree `q + q`. -/
theorem isHomogeneous_coherentHomotopy {ι σM σN : Type*} [AddMonoid ι]
    [SetLike σM M] [SetLike σN N] [AddMemClass σN N] [NegMemClass σN N]
    {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι}
    (hf : LinearMap.IsHomogeneous e.hom 𝒜 ℬ 0)
    (hhM : LinearMap.IsHomogeneous e.homotopyHom 𝒜 𝒜 q)
    (hhN : LinearMap.IsHomogeneous e.homotopyInv ℬ ℬ q) :
    LinearMap.IsHomogeneous e.coherentHomotopy 𝒜 ℬ (q + q) := by
  rw [coherentHomotopy_def]
  have hδ : LinearMap.IsHomogeneous (e.hom ∘ₗ e.homotopyHom - e.homotopyInv ∘ₗ e.hom) 𝒜 ℬ q :=
    LinearMap.IsHomogeneous.sub (by simpa only [add_zero] using hf.comp hhM)
      (by simpa only [zero_add] using hhN.comp hf)
  exact (hδ.comp hhM).neg

end Adjoint

/-! ### Solving coupled Hom-complex equations -/

section Coupled

variable {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN)
  {P : Type uP} [AddCommGroup P] [Module R P]

/-- The explicit lift `inv ∘ v + homotopyHom ∘ u` solving `dM ∘ x + s • (x ∘ dP) = u` when `u` is a
cocycle in `Hom(P, M)` and `v` bounds `hom ∘ u` in `Hom(P, N)`. -/
def coupledLift (u : P →ₗ[R] M) (v : P →ₗ[R] N) : P →ₗ[R] M :=
  e.inv ∘ₗ v + e.homotopyHom ∘ₗ u

theorem coupledLift_def (u : P →ₗ[R] M) (v : P →ₗ[R] N) :
    e.coupledLift u v = e.inv ∘ₗ v + e.homotopyHom ∘ₗ u :=
  (rfl)

/-- The explicit homotopy `adjointHomotopyInv ∘ v - coherentHomotopy ∘ u` bounding the defect
`v - hom ∘ coupledLift u v` in `Hom(P, N)`. -/
def coupledHomotopy (u : P →ₗ[R] M) (v : P →ₗ[R] N) : P →ₗ[R] N :=
  e.adjointHomotopyInv ∘ₗ v - e.coherentHomotopy ∘ₗ u

theorem coupledHomotopy_def (u : P →ₗ[R] M) (v : P →ₗ[R] N) :
    e.coupledHomotopy u v = e.adjointHomotopyInv ∘ₗ v - e.coherentHomotopy ∘ₗ u :=
  (rfl)

/-- First coupled Hom-complex equation: if `dM ∘ u = s • (u ∘ dP)` and
`dN ∘ v + s • (v ∘ dP) = hom ∘ u`, then `coupledLift u v` bounds `u`. -/
theorem dM_comp_coupledLift_add_smul {dP : Module.End R P} {s : ℤˣ}
    {u : P →ₗ[R] M} {v : P →ₗ[R] N}
    (hu : dM ∘ₗ u - s • (u ∘ₗ dP) = 0) (hv : dN ∘ₗ v + s • (v ∘ₗ dP) = e.hom ∘ₗ u) :
    dM ∘ₗ e.coupledLift u v + s • (e.coupledLift u v ∘ₗ dP) = u := by
  have hu' : s • (u ∘ₗ dP) = dM ∘ₗ u := (sub_eq_zero.1 hu).symm
  have hdist : s • ((e.inv ∘ₗ v + e.homotopyHom ∘ₗ u) ∘ₗ dP) =
      e.inv ∘ₗ (s • (v ∘ₗ dP)) + e.homotopyHom ∘ₗ (s • (u ∘ₗ dP)) := by
    simp only [LinearMap.add_comp, smul_add, LinearMap.comp_assoc, Units.smul_def,
      LinearMap.comp_smul]
  calc
    dM ∘ₗ e.coupledLift u v + s • (e.coupledLift u v ∘ₗ dP)
      = e.inv ∘ₗ (dN ∘ₗ v + s • (v ∘ₗ dP)) +
          (dM ∘ₗ e.homotopyHom ∘ₗ u + e.homotopyHom ∘ₗ (s • (u ∘ₗ dP))) := by
        rw [coupledLift_def, LinearMap.comp_add, hdist, e.dM_comp_inv_assoc, LinearMap.comp_add]
        abel
    _ = e.inv ∘ₗ e.hom ∘ₗ u + (dM ∘ₗ e.homotopyHom + e.homotopyHom ∘ₗ dM) ∘ₗ u := by
        rw [hv, hu', LinearMap.add_comp, LinearMap.comp_assoc, LinearMap.comp_assoc]
    _ = u := by
        rw [e.dM_comp_homotopyHom_add_homotopyHom_comp_dM, LinearMap.sub_comp, LinearMap.id_comp,
          LinearMap.comp_assoc, add_sub_cancel]

/-- Second coupled Hom-complex equation: under the same hypotheses, `coupledHomotopy u v` bounds
`v - hom ∘ coupledLift u v`. -/
theorem sub_hom_comp_coupledLift {dP : Module.End R P} {s : ℤˣ}
    {u : P →ₗ[R] M} {v : P →ₗ[R] N}
    (hu : dM ∘ₗ u - s • (u ∘ₗ dP) = 0) (hv : dN ∘ₗ v + s • (v ∘ₗ dP) = e.hom ∘ₗ u) :
    v - e.hom ∘ₗ e.coupledLift u v =
      dN ∘ₗ e.coupledHomotopy u v - s • (e.coupledHomotopy u v ∘ₗ dP) := by
  have hu' : s • (u ∘ₗ dP) = dM ∘ₗ u := (sub_eq_zero.1 hu).symm
  have hv' : s • (v ∘ₗ dP) = e.hom ∘ₗ u - dN ∘ₗ v := eq_sub_of_add_eq' hv
  have hdist : s • ((e.adjointHomotopyInv ∘ₗ v - e.coherentHomotopy ∘ₗ u) ∘ₗ dP) =
      e.adjointHomotopyInv ∘ₗ (s • (v ∘ₗ dP)) - e.coherentHomotopy ∘ₗ (s • (u ∘ₗ dP)) := by
    simp only [LinearMap.sub_comp, smul_sub, LinearMap.comp_assoc, Units.smul_def,
      LinearMap.comp_smul]
  symm
  calc
    dN ∘ₗ e.coupledHomotopy u v - s • (e.coupledHomotopy u v ∘ₗ dP)
      = dN ∘ₗ e.adjointHomotopyInv ∘ₗ v - e.adjointHomotopyInv ∘ₗ (s • (v ∘ₗ dP)) -
          dN ∘ₗ e.coherentHomotopy ∘ₗ u + e.coherentHomotopy ∘ₗ (s • (u ∘ₗ dP)) := by
        simp only [coupledHomotopy_def, LinearMap.comp_sub, hdist]
        abel
    _ = (dN ∘ₗ e.adjointHomotopyInv + e.adjointHomotopyInv ∘ₗ dN) ∘ₗ v -
          e.adjointHomotopyInv ∘ₗ e.hom ∘ₗ u -
          (dN ∘ₗ e.coherentHomotopy - e.coherentHomotopy ∘ₗ dM) ∘ₗ u := by
        rw [hv', hu', LinearMap.comp_sub, LinearMap.add_comp, LinearMap.sub_comp]
        simp only [LinearMap.comp_assoc]
        abel
    _ = (LinearMap.id - e.hom ∘ₗ e.inv) ∘ₗ v - e.adjointHomotopyInv ∘ₗ e.hom ∘ₗ u -
          (e.hom ∘ₗ e.homotopyHom - e.adjointHomotopyInv ∘ₗ e.hom) ∘ₗ u := by
        rw [e.dN_comp_adjointHomotopyInv_add_adjointHomotopyInv_comp_dN,
          ← e.hom_comp_homotopyHom_sub_adjointHomotopyInv_comp_hom]
    _ = v - e.hom ∘ₗ e.coupledLift u v := by
        rw [coupledLift_def, LinearMap.comp_add]
        simp only [LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc]
        abel

/-- If `inv` has degree zero, `homotopyHom` has degree `-q`, `u` has degree `r + q`, and `v` has
degree `r`, then `coupledLift u v` has degree `r`. -/
theorem isHomogeneous_coupledLift {ι σP σM σN : Type*} [AddGroup ι]
    [SetLike σP P] [SetLike σM M] [AddMemClass σM M] [SetLike σN N]
    {𝒞 : ι → σP} {𝒜 : ι → σM} {ℬ : ι → σN} {q r : ι} {u : P →ₗ[R] M} {v : P →ₗ[R] N}
    (hg : LinearMap.IsHomogeneous e.inv ℬ 𝒜 0)
    (hhM : LinearMap.IsHomogeneous e.homotopyHom 𝒜 𝒜 (-q))
    (hu : LinearMap.IsHomogeneous u 𝒞 𝒜 (r + q))
    (hv : LinearMap.IsHomogeneous v 𝒞 ℬ r) :
    LinearMap.IsHomogeneous (e.coupledLift u v) 𝒞 𝒜 r := by
  rw [coupledLift_def]
  exact LinearMap.IsHomogeneous.add (by simpa only [add_zero] using hg.comp hv)
    (by simpa only [add_neg_cancel_right] using hhM.comp hu)

/-- If `hom` and `inv` have degree zero, both homotopies have degree `-q`, `u` has degree `r + q`,
and `v` has degree `r`, then `coupledHomotopy u v` has degree `r - q`. -/
theorem isHomogeneous_coupledHomotopy {ι σP σM σN : Type*} [AddGroup ι]
    [SetLike σP P] [SetLike σM M] [SetLike σN N] [AddMemClass σN N] [NegMemClass σN N]
    {𝒞 : ι → σP} {𝒜 : ι → σM} {ℬ : ι → σN} {q r : ι} {u : P →ₗ[R] M} {v : P →ₗ[R] N}
    (hf : LinearMap.IsHomogeneous e.hom 𝒜 ℬ 0)
    (hg : LinearMap.IsHomogeneous e.inv ℬ 𝒜 0)
    (hhM : LinearMap.IsHomogeneous e.homotopyHom 𝒜 𝒜 (-q))
    (hhN : LinearMap.IsHomogeneous e.homotopyInv ℬ ℬ (-q))
    (hu : LinearMap.IsHomogeneous u 𝒞 𝒜 (r + q))
    (hv : LinearMap.IsHomogeneous v 𝒞 ℬ r) :
    LinearMap.IsHomogeneous (e.coupledHomotopy u v) 𝒞 ℬ (r - q) := by
  rw [coupledHomotopy_def]
  have hk' := e.isHomogeneous_adjointHomotopyInv hf hg hhM hhN
  have hm := e.isHomogeneous_coherentHomotopy hf hhM hhN
  have hdeg : r + q + (-q + -q) = r - q := by
    rw [← add_assoc, add_neg_cancel_right, sub_eq_add_neg]
  exact LinearMap.IsHomogeneous.sub (by simpa only [sub_eq_add_neg] using hk'.comp hv)
    (by rw [← hdeg]; exact hm.comp hu)

end Coupled

end LinearHomotopyEquiv

/-! ### Viewing a contraction as a homotopy equivalence -/

namespace LinearContraction

variable {dM : Module.End R M} {dN : Module.End R N} (c : LinearContraction dM dN)

/-- View a linear contraction of `(M, dM)` onto `(N, dN)` as a linear homotopy equivalence with
forward map `proj`, inverse `incl`, and `homotopyInv = 0`. -/
def toLinearHomotopyEquiv : LinearHomotopyEquiv dM dN where
  hom := c.proj
  inv := c.incl
  homotopyHom := c.homotopy
  homotopyInv := 0
  dN_comp_hom := c.proj_comp_dM.symm
  dM_comp_inv := c.dM_comp_incl
  dM_comp_homotopyHom_add_homotopyHom_comp_dM := c.dM_comp_homotopy_add_homotopy_comp_dM
  dN_comp_homotopyInv_add_homotopyInv_comp_dN := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp, add_zero, c.proj_comp_incl, sub_self]

@[simp] theorem toLinearHomotopyEquiv_hom : c.toLinearHomotopyEquiv.hom = c.proj := (rfl)
@[simp] theorem toLinearHomotopyEquiv_inv : c.toLinearHomotopyEquiv.inv = c.incl := (rfl)
@[simp] theorem toLinearHomotopyEquiv_homotopyHom :
    c.toLinearHomotopyEquiv.homotopyHom = c.homotopy := (rfl)
@[simp] theorem toLinearHomotopyEquiv_homotopyInv :
    c.toLinearHomotopyEquiv.homotopyInv = 0 := (rfl)

end LinearContraction

end Semiring

/-! ### Induced equivalence on homology -/

section Homology

variable {R : Type uR} {M : Type uM} {N : Type uN} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearHomotopyEquiv

variable {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN)

/-- On homology, `inv ∘ hom` induces the identity map. -/
theorem homologyMap_inv_comp_homologyMap_hom (hdM : dM ∘ₗ dM = 0) (hdN : dN ∘ₗ dN = 0) :
    _root_.LinearMap.homologyMap e.inv hdN hdM e.inv_comp_dN ∘ₗ
        _root_.LinearMap.homologyMap e.hom hdM hdN e.hom_comp_dM =
      LinearMap.id := by
  rw [_root_.LinearMap.homologyMap_comp_homologyMap]
  ext m
  have hsub : _root_.LinearMap.homologyMap (LinearMap.id - e.inv ∘ₗ e.hom) hdM hdM
      (by rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp, LinearMap.comp_id,
        LinearMap.comp_assoc, e.hom_comp_dM, ← LinearMap.comp_assoc, e.inv_comp_dN,
        LinearMap.comp_assoc]) (Submodule.Quotient.mk m) = 0 := by
    rw [_root_.LinearMap.homologyMap_mk, ← dM.homologyπ_apply hdM, dM.homologyπ_eq_zero_iff hdM]
    refine ⟨e.homotopyHom m, ?_⟩
    have hm := LinearMap.congr_fun e.dM_comp_homotopyHom_add_homotopyHom_comp_dM m
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.coe_subtype, LinearMap.mem_ker.1 m.2, map_zero, add_zero]
      using hm
  rw [_root_.LinearMap.homologyMap_sub LinearMap.id (e.inv ∘ₗ e.hom) hdM hdM (by simp) _,
    _root_.LinearMap.homologyMap_id, LinearMap.sub_apply, sub_eq_zero] at hsub
  exact hsub.symm

/-- On homology, `hom ∘ inv` induces the identity map. -/
theorem homologyMap_hom_comp_homologyMap_inv (hdM : dM ∘ₗ dM = 0) (hdN : dN ∘ₗ dN = 0) :
    _root_.LinearMap.homologyMap e.hom hdM hdN e.hom_comp_dM ∘ₗ
        _root_.LinearMap.homologyMap e.inv hdN hdM e.inv_comp_dN =
      LinearMap.id :=
  e.symm.homologyMap_inv_comp_homologyMap_hom hdN hdM

/-- For square-zero endomorphisms `dM` and `dN`, a linear homotopy equivalence induces a linear
equivalence between `dM.homology hdM` and `dN.homology hdN`. -/
noncomputable def homologyEquiv (hdM : dM ∘ₗ dM = 0) (hdN : dN ∘ₗ dN = 0) :
    dM.homology hdM ≃ₗ[R] dN.homology hdN :=
  LinearEquiv.ofLinearMap
    (_root_.LinearMap.homologyMap e.hom hdM hdN e.hom_comp_dM)
    (_root_.LinearMap.homologyMap e.inv hdN hdM e.inv_comp_dN)
    (e.homologyMap_hom_comp_homologyMap_inv hdM hdN)
    (e.homologyMap_inv_comp_homologyMap_hom hdM hdN)

@[simp]
theorem toLinearMap_homologyEquiv (hdM : dM ∘ₗ dM = 0) (hdN : dN ∘ₗ dN = 0) :
    (e.homologyEquiv hdM hdN).toLinearMap =
      _root_.LinearMap.homologyMap e.hom hdM hdN e.hom_comp_dM :=
  (rfl)

@[simp]
theorem symm_homologyEquiv (hdM : dM ∘ₗ dM = 0) (hdN : dN ∘ₗ dN = 0) :
    (e.homologyEquiv hdM hdN).symm = e.symm.homologyEquiv hdN hdM :=
  (rfl)

end LinearHomotopyEquiv

end Homology

end TauCeti
