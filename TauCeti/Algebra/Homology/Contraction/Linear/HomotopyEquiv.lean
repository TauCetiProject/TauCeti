/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
import Mathlib.Tactic.Abel

/-!
# Chain-homotopy equivalences of modules with a differential

`LinearHomotopyEquiv dM dN` packages a two-sided chain-homotopy equivalence between modules `M`
and `N` equipped with endomorphisms `dM` and `dN`: linear maps `hom : M →ₗ[R] N` and
`inv : N →ₗ[R] M` intertwining `dM` and `dN`, together with homotopies `homotopyInvHom` on `M` and
`homotopyHomInv` on `N` satisfying

`dM ∘ homotopyInvHom + homotopyInvHom ∘ dM = inv ∘ hom - 1`,
`dN ∘ homotopyHomInv + homotopyHomInv ∘ dN = hom ∘ inv - 1`.

Like `TauCeti.LinearContraction`, this operates on the total module rather than on degreewise
cochain complexes, and does not assume `dM² = 0` or `dN² = 0`; compatibility with an internal
grading is expressed separately by `LinearHomotopyEquiv.IsHomogeneous`, which requires `hom` and
`inv` to have degree zero and both homotopies to shift degree by a given `r` (typically `-1` in
cohomological grading).  Every `LinearContraction` gives a `LinearHomotopyEquiv` with
`hom := proj`, `inv := incl`, `homotopyInvHom := -homotopy`, and `homotopyHomInv := 0`.

## Main definitions

* `TauCeti.LinearHomotopyEquiv`: a two-sided chain-homotopy equivalence between `(M, dM)` and
  `(N, dN)`.
* `TauCeti.LinearHomotopyEquiv.IsHomogeneous`: homogeneity of `hom` and `inv` of degree zero and
  of both homotopies of degree `r`.
* `TauCeti.LinearHomotopyEquiv.refl`, `symm`, `trans`: reflexivity, symmetry, and transitivity of
  chain-homotopy equivalences.
* `TauCeti.LinearHomotopyEquiv.ofLinearEquiv`: a differential-intertwining linear equivalence as a
  chain-homotopy equivalence with zero homotopies.
* `TauCeti.LinearHomotopyEquiv.ofHomotopy`: replacing the forward map by a chain-homotopic chain
  map.
* `TauCeti.LinearContraction.toLinearHomotopyEquiv`: the chain-homotopy equivalence underlying a
  contraction.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Section 1.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 1.5.
-/

public section

universe uR uM uN uP

namespace TauCeti

variable {R : Type uR} {M : Type uM} {N : Type uN} {P : Type uP} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A two-sided chain-homotopy equivalence between modules `(M, dM)` and `(N, dN)` equipped with
endomorphisms.  For square-zero endomorphisms this is a chain-homotopy equivalence of differential
modules; the sign convention `d h + h d = g ∘ f - 1` matches `TauCeti.AInfinityHom.Homotopy` for a
homotopy from `g ∘ f` to the identity. -/
@[ext]
structure LinearHomotopyEquiv (dM : Module.End R M) (dN : Module.End R N) where
  /-- The forward chain map. -/
  hom : M →ₗ[R] N
  /-- The inverse chain map. -/
  inv : N →ₗ[R] M
  /-- The homotopy on `M` witnessing `inv ∘ hom ≃ 1`. -/
  homotopyInvHom : Module.End R M
  /-- The homotopy on `N` witnessing `hom ∘ inv ≃ 1`. -/
  homotopyHomInv : Module.End R N
  /-- The forward map intertwines the endomorphisms. -/
  dN_comp_hom : dN ∘ₗ hom = hom ∘ₗ dM
  /-- The inverse map intertwines the endomorphisms. -/
  dM_comp_inv : dM ∘ₗ inv = inv ∘ₗ dN
  /-- The homotopy equation `dM h_M + h_M dM = inv ∘ hom - 1` on `M`. -/
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM :
    dM ∘ₗ homotopyInvHom + homotopyInvHom ∘ₗ dM = inv ∘ₗ hom - LinearMap.id
  /-- The homotopy equation `dN h_N + h_N dN = hom ∘ inv - 1` on `N`. -/
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN :
    dN ∘ₗ homotopyHomInv + homotopyHomInv ∘ₗ dN = hom ∘ₗ inv - LinearMap.id

namespace LinearHomotopyEquiv

attribute [simp] dN_comp_hom dM_comp_inv

section Basic

variable {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN)

@[simp]
theorem dN_hom_apply (x : M) : dN (e.hom x) = e.hom (dM x) :=
  LinearMap.congr_fun e.dN_comp_hom x

@[simp]
theorem dM_inv_apply (y : N) : dM (e.inv y) = e.inv (dN y) :=
  LinearMap.congr_fun e.dM_comp_inv y

/-- Express `inv ∘ hom` as `1 + dM ∘ homotopyInvHom + homotopyInvHom ∘ dM`. -/
theorem inv_comp_hom :
    e.inv ∘ₗ e.hom = LinearMap.id + (dM ∘ₗ e.homotopyInvHom + e.homotopyInvHom ∘ₗ dM) := by
  rw [e.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM, add_sub_cancel]

/-- Express `hom ∘ inv` as `1 + dN ∘ homotopyHomInv + homotopyHomInv ∘ dN`. -/
theorem hom_comp_inv :
    e.hom ∘ₗ e.inv = LinearMap.id + (dN ∘ₗ e.homotopyHomInv + e.homotopyHomInv ∘ₗ dN) := by
  rw [e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN, add_sub_cancel]

/-- A chain-homotopy equivalence is homogeneous with homotopy degree `r` when `hom` and `inv` have
degree zero and both homotopies have degree `r`. -/
structure IsHomogeneous {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    (e : LinearHomotopyEquiv dM dN) (𝒜 : ι → σM) (ℬ : ι → σN) (r : ι) : Prop where
  /-- The forward chain map has degree zero. -/
  hom : LinearMap.IsHomogeneous e.hom 𝒜 ℬ 0
  /-- The inverse chain map has degree zero. -/
  inv : LinearMap.IsHomogeneous e.inv ℬ 𝒜 0
  /-- The homotopy on `M` has degree `r`. -/
  homotopyInvHom : LinearMap.IsHomogeneous e.homotopyInvHom 𝒜 𝒜 r
  /-- The homotopy on `N` has degree `r`. -/
  homotopyHomInv : LinearMap.IsHomogeneous e.homotopyHomInv ℬ ℬ r

end Basic

/-! ### Constructions and operations -/

/-- The identity chain-homotopy equivalence of `(M, dM)` with zero homotopies. -/
def refl (dM : Module.End R M) : LinearHomotopyEquiv dM dM where
  hom := LinearMap.id
  inv := LinearMap.id
  homotopyInvHom := 0
  homotopyHomInv := 0
  dN_comp_hom := by rw [LinearMap.comp_id, LinearMap.id_comp]
  dM_comp_inv := by rw [LinearMap.comp_id, LinearMap.id_comp]
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp, add_zero, LinearMap.id_comp, sub_self]
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp, add_zero, LinearMap.id_comp, sub_self]

@[simp] theorem hom_refl (dM : Module.End R M) : (refl dM).hom = LinearMap.id := (rfl)
@[simp] theorem inv_refl (dM : Module.End R M) : (refl dM).inv = LinearMap.id := (rfl)
@[simp] theorem homotopyInvHom_refl (dM : Module.End R M) : (refl dM).homotopyInvHom = 0 := (rfl)
@[simp] theorem homotopyHomInv_refl (dM : Module.End R M) : (refl dM).homotopyHomInv = 0 := (rfl)

/-- The identity chain-homotopy equivalence is homogeneous of any homotopy degree `r`. -/
theorem isHomogeneous_refl {ι σM : Type*} [AddMonoid ι] [SetLike σM M] [ZeroMemClass σM M]
    (dM : Module.End R M) (𝒜 : ι → σM) (r : ι) :
    (refl dM).IsHomogeneous 𝒜 𝒜 r :=
  ⟨LinearMap.isHomogeneous_id 𝒜, LinearMap.isHomogeneous_id 𝒜,
    LinearMap.isHomogeneous_zero 𝒜 𝒜 r, LinearMap.isHomogeneous_zero 𝒜 𝒜 r⟩

/-- Swap the forward and inverse maps of a chain-homotopy equivalence. -/
def symm {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN) :
    LinearHomotopyEquiv dN dM where
  hom := e.inv
  inv := e.hom
  homotopyInvHom := e.homotopyHomInv
  homotopyHomInv := e.homotopyInvHom
  dN_comp_hom := e.dM_comp_inv
  dM_comp_inv := e.dN_comp_hom
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM :=
    e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN :=
    e.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM

@[simp]
theorem hom_symm {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN) :
    e.symm.hom = e.inv := (rfl)

@[simp]
theorem inv_symm {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN) :
    e.symm.inv = e.hom := (rfl)

@[simp]
theorem homotopyInvHom_symm {dM : Module.End R M} {dN : Module.End R N}
    (e : LinearHomotopyEquiv dM dN) :
    e.symm.homotopyInvHom = e.homotopyHomInv := (rfl)

@[simp]
theorem homotopyHomInv_symm {dM : Module.End R M} {dN : Module.End R N}
    (e : LinearHomotopyEquiv dM dN) :
    e.symm.homotopyHomInv = e.homotopyInvHom := (rfl)

/-- Swapping forward and inverse maps preserves homogeneity of a chain-homotopy equivalence. -/
theorem IsHomogeneous.symm {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    {dM : Module.End R M} {dN : Module.End R N} {e : LinearHomotopyEquiv dM dN}
    {𝒜 : ι → σM} {ℬ : ι → σN} {r : ι} (he : e.IsHomogeneous 𝒜 ℬ r) :
    e.symm.IsHomogeneous ℬ 𝒜 r :=
  ⟨he.inv, he.hom, he.homotopyHomInv, he.homotopyInvHom⟩

/-- Compose two chain-homotopy equivalences. -/
def trans {dM : Module.End R M} {dN : Module.End R N} {dP : Module.End R P}
    (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
    LinearHomotopyEquiv dM dP where
  hom := e₂.hom ∘ₗ e₁.hom
  inv := e₁.inv ∘ₗ e₂.inv
  homotopyInvHom := e₁.inv ∘ₗ e₂.homotopyInvHom ∘ₗ e₁.hom + e₁.homotopyInvHom
  homotopyHomInv := e₂.hom ∘ₗ e₁.homotopyHomInv ∘ₗ e₂.inv + e₂.homotopyHomInv
  dN_comp_hom := by
    rw [← LinearMap.comp_assoc, e₂.dN_comp_hom, LinearMap.comp_assoc, e₁.dN_comp_hom,
      LinearMap.comp_assoc]
  dM_comp_inv := by
    rw [← LinearMap.comp_assoc, e₁.dM_comp_inv, LinearMap.comp_assoc, e₂.dM_comp_inv,
      LinearMap.comp_assoc]
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by
    have h₁ : dM ∘ₗ (e₁.inv ∘ₗ e₂.homotopyInvHom ∘ₗ e₁.hom) +
        (e₁.inv ∘ₗ e₂.homotopyInvHom ∘ₗ e₁.hom) ∘ₗ dM =
        e₁.inv ∘ₗ (dN ∘ₗ e₂.homotopyInvHom + e₂.homotopyInvHom ∘ₗ dN) ∘ₗ e₁.hom :=
      LinearMap.ext fun x ↦ by
        simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, e₁.dM_inv_apply,
          ← e₁.dN_hom_apply]
    rw [LinearMap.comp_add, LinearMap.add_comp, add_add_add_comm, h₁,
      e₂.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM,
      e₁.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM, LinearMap.sub_comp, LinearMap.comp_sub,
      LinearMap.id_comp]
    simp only [LinearMap.comp_assoc]
    abel
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by
    have h₂ : dP ∘ₗ (e₂.hom ∘ₗ e₁.homotopyHomInv ∘ₗ e₂.inv) +
        (e₂.hom ∘ₗ e₁.homotopyHomInv ∘ₗ e₂.inv) ∘ₗ dP =
        e₂.hom ∘ₗ (dN ∘ₗ e₁.homotopyHomInv + e₁.homotopyHomInv ∘ₗ dN) ∘ₗ e₂.inv :=
      LinearMap.ext fun z ↦ by
        simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, e₂.dN_hom_apply,
          ← e₂.dM_inv_apply]
    rw [LinearMap.comp_add, LinearMap.add_comp, add_add_add_comm, h₂,
      e₁.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN,
      e₂.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN, LinearMap.sub_comp, LinearMap.comp_sub,
      LinearMap.id_comp]
    simp only [LinearMap.comp_assoc]
    abel

@[simp]
theorem hom_trans {dM : Module.End R M} {dN : Module.End R N} {dP : Module.End R P}
    (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).hom = e₂.hom ∘ₗ e₁.hom := (rfl)

@[simp]
theorem inv_trans {dM : Module.End R M} {dN : Module.End R N} {dP : Module.End R P}
    (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).inv = e₁.inv ∘ₗ e₂.inv := (rfl)

@[simp]
theorem homotopyInvHom_trans {dM : Module.End R M} {dN : Module.End R N} {dP : Module.End R P}
    (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).homotopyInvHom =
      e₁.inv ∘ₗ e₂.homotopyInvHom ∘ₗ e₁.hom + e₁.homotopyInvHom := (rfl)

@[simp]
theorem homotopyHomInv_trans {dM : Module.End R M} {dN : Module.End R N} {dP : Module.End R P}
    (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).homotopyHomInv =
      e₂.hom ∘ₗ e₁.homotopyHomInv ∘ₗ e₂.inv + e₂.homotopyHomInv := (rfl)

/-- Composing two homogeneous chain-homotopy equivalences of homotopy degree `r` yields a
homogeneous chain-homotopy equivalence of homotopy degree `r`. -/
theorem IsHomogeneous.trans {ι σM σN σP : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    [SetLike σP P] [AddMemClass σM M] [AddMemClass σP P]
    {dM : Module.End R M} {dN : Module.End R N} {dP : Module.End R P}
    {e₁ : LinearHomotopyEquiv dM dN} {e₂ : LinearHomotopyEquiv dN dP}
    {𝒜 : ι → σM} {ℬ : ι → σN} {𝒞 : ι → σP} {r : ι}
    (h₁ : e₁.IsHomogeneous 𝒜 ℬ r) (h₂ : e₂.IsHomogeneous ℬ 𝒞 r) :
    (e₁.trans e₂).IsHomogeneous 𝒜 𝒞 r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hom_trans]
    simpa only [add_zero] using h₂.hom.comp h₁.hom
  · rw [inv_trans]
    simpa only [add_zero] using h₁.inv.comp h₂.inv
  · rw [homotopyInvHom_trans]
    refine LinearMap.IsHomogeneous.add ?_ h₁.homotopyInvHom
    simpa only [zero_add, add_zero] using h₁.inv.comp (h₂.homotopyInvHom.comp h₁.hom)
  · rw [homotopyHomInv_trans]
    refine LinearMap.IsHomogeneous.add ?_ h₂.homotopyHomInv
    simpa only [zero_add, add_zero] using h₂.hom.comp (h₁.homotopyHomInv.comp h₂.inv)

/-- A linear equivalence intertwining `dM` and `dN` gives a chain-homotopy equivalence with zero
homotopies. -/
def ofLinearEquiv {dM : Module.End R M} {dN : Module.End R N} (e : M ≃ₗ[R] N)
    (hd : dN ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ dM) : LinearHomotopyEquiv dM dN where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  homotopyInvHom := 0
  homotopyHomInv := 0
  dN_comp_hom := hd
  dM_comp_inv := by
    refine LinearMap.ext fun y ↦ e.injective ?_
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, e.apply_symm_apply] using
      (LinearMap.congr_fun hd (e.symm y)).symm
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp, add_zero, e.symm_comp, sub_self]
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp, add_zero, e.comp_symm, sub_self]

@[simp]
theorem hom_ofLinearEquiv {dM : Module.End R M} {dN : Module.End R N} (e : M ≃ₗ[R] N)
    (hd : dN ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ dM) :
    (ofLinearEquiv e hd).hom = e.toLinearMap := (rfl)

@[simp]
theorem inv_ofLinearEquiv {dM : Module.End R M} {dN : Module.End R N} (e : M ≃ₗ[R] N)
    (hd : dN ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ dM) :
    (ofLinearEquiv e hd).inv = e.symm.toLinearMap := (rfl)

/-- A degree-zero linear equivalence intertwining the differentials yields a homogeneous
chain-homotopy equivalence of any homotopy degree `r`. -/
theorem isHomogeneous_ofLinearEquiv {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    [ZeroMemClass σM M] [ZeroMemClass σN N] {dM : Module.End R M} {dN : Module.End R N}
    {e : M ≃ₗ[R] N} (hd : dN ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ dM)
    {𝒜 : ι → σM} {ℬ : ι → σN} (he : LinearMap.IsHomogeneous e.toLinearMap 𝒜 ℬ 0)
    (he' : LinearMap.IsHomogeneous e.symm.toLinearMap ℬ 𝒜 0) (r : ι) :
    (ofLinearEquiv e hd).IsHomogeneous 𝒜 ℬ r :=
  ⟨he, he', LinearMap.isHomogeneous_zero 𝒜 𝒜 r, LinearMap.isHomogeneous_zero ℬ ℬ r⟩

/-- Replace the forward map `e.hom` of a chain-homotopy equivalence by a chain map `f'` satisfying
`e.hom - f' = dN ∘ s + s ∘ dM`, keeping the same inverse map `e.inv`. -/
def ofHomotopy {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN)
    {f' : M →ₗ[R] N} (hf' : dN ∘ₗ f' = f' ∘ₗ dM) (s : M →ₗ[R] N)
    (hs : e.hom - f' = dN ∘ₗ s + s ∘ₗ dM) : LinearHomotopyEquiv dM dN where
  hom := f'
  inv := e.inv
  homotopyInvHom := e.homotopyInvHom - e.inv ∘ₗ s
  homotopyHomInv := e.homotopyHomInv - s ∘ₗ e.inv
  dN_comp_hom := hf'
  dM_comp_inv := e.dM_comp_inv
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by
    have h₁ : dM ∘ₗ (e.inv ∘ₗ s) + (e.inv ∘ₗ s) ∘ₗ dM = e.inv ∘ₗ (e.hom - f') := by
      rw [← LinearMap.comp_assoc, e.dM_comp_inv, LinearMap.comp_assoc, LinearMap.comp_assoc,
        ← LinearMap.comp_add, ← hs]
    rw [LinearMap.comp_sub, LinearMap.sub_comp, sub_add_sub_comm,
      e.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM, h₁, LinearMap.comp_sub]
    abel
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by
    have h₂ : dN ∘ₗ (s ∘ₗ e.inv) + (s ∘ₗ e.inv) ∘ₗ dN = (e.hom - f') ∘ₗ e.inv := by
      rw [LinearMap.comp_assoc, e.dM_comp_inv.symm, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
        ← LinearMap.add_comp, ← hs]
    rw [LinearMap.comp_sub, LinearMap.sub_comp, sub_add_sub_comm,
      e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN, h₂, LinearMap.sub_comp]
    abel

@[simp]
theorem hom_ofHomotopy {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN)
    {f' : M →ₗ[R] N} (hf' : dN ∘ₗ f' = f' ∘ₗ dM) (s : M →ₗ[R] N)
    (hs : e.hom - f' = dN ∘ₗ s + s ∘ₗ dM) :
    (e.ofHomotopy hf' s hs).hom = f' := (rfl)

@[simp]
theorem inv_ofHomotopy {dM : Module.End R M} {dN : Module.End R N} (e : LinearHomotopyEquiv dM dN)
    {f' : M →ₗ[R] N} (hf' : dN ∘ₗ f' = f' ∘ₗ dM) (s : M →ₗ[R] N)
    (hs : e.hom - f' = dN ∘ₗ s + s ∘ₗ dM) :
    (e.ofHomotopy hf' s hs).inv = e.inv := (rfl)

@[simp]
theorem homotopyInvHom_ofHomotopy {dM : Module.End R M} {dN : Module.End R N}
    (e : LinearHomotopyEquiv dM dN) {f' : M →ₗ[R] N} (hf' : dN ∘ₗ f' = f' ∘ₗ dM)
    (s : M →ₗ[R] N) (hs : e.hom - f' = dN ∘ₗ s + s ∘ₗ dM) :
    (e.ofHomotopy hf' s hs).homotopyInvHom = e.homotopyInvHom - e.inv ∘ₗ s := (rfl)

@[simp]
theorem homotopyHomInv_ofHomotopy {dM : Module.End R M} {dN : Module.End R N}
    (e : LinearHomotopyEquiv dM dN) {f' : M →ₗ[R] N} (hf' : dN ∘ₗ f' = f' ∘ₗ dM)
    (s : M →ₗ[R] N) (hs : e.hom - f' = dN ∘ₗ s + s ∘ₗ dM) :
    (e.ofHomotopy hf' s hs).homotopyHomInv = e.homotopyHomInv - s ∘ₗ e.inv := (rfl)

/-- Transporting the forward map along a degree-`r` chain homotopy preserves homogeneity. -/
theorem IsHomogeneous.ofHomotopy {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    [AddMemClass σM M] [NegMemClass σM M] [AddMemClass σN N] [NegMemClass σN N]
    {dM : Module.End R M} {dN : Module.End R N} {e : LinearHomotopyEquiv dM dN}
    {𝒜 : ι → σM} {ℬ : ι → σN} {r : ι} (he : e.IsHomogeneous 𝒜 ℬ r)
    {f' : M →ₗ[R] N} (hf' : dN ∘ₗ f' = f' ∘ₗ dM)
    (hf'₀ : LinearMap.IsHomogeneous f' 𝒜 ℬ 0) {s : M →ₗ[R] N}
    (hs₀ : LinearMap.IsHomogeneous s 𝒜 ℬ r)
    (hs : e.hom - f' = dN ∘ₗ s + s ∘ₗ dM) :
    (e.ofHomotopy hf' s hs).IsHomogeneous 𝒜 ℬ r := by
  refine ⟨hf'₀, he.inv, ?_, ?_⟩
  · rw [homotopyInvHom_ofHomotopy]
    exact he.homotopyInvHom.sub (by simpa only [add_zero] using he.inv.comp hs₀)
  · rw [homotopyHomInv_ofHomotopy]
    exact he.homotopyHomInv.sub (by simpa only [zero_add] using hs₀.comp he.inv)

end LinearHomotopyEquiv

namespace LinearContraction

/-- View a contraction of `(M, dM)` onto `(N, dN)` as a chain-homotopy equivalence with forward map
`proj`, inverse map `incl`, homotopy `-homotopy` on `M`, and zero homotopy on `N`. -/
def toLinearHomotopyEquiv {dM : Module.End R M} {dN : Module.End R N}
    (c : LinearContraction dM dN) : LinearHomotopyEquiv dM dN where
  hom := c.proj
  inv := c.incl
  homotopyInvHom := -c.homotopy
  homotopyHomInv := 0
  dN_comp_hom := c.proj_comp_dM.symm
  dM_comp_inv := c.dM_comp_incl
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by
    rw [LinearMap.comp_neg, LinearMap.neg_comp, ← neg_add,
      c.dM_comp_homotopy_add_homotopy_comp_dM, neg_sub]
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp, add_zero, c.proj_comp_incl, sub_self]

@[simp]
theorem hom_toLinearHomotopyEquiv {dM : Module.End R M} {dN : Module.End R N}
    (c : LinearContraction dM dN) : c.toLinearHomotopyEquiv.hom = c.proj := (rfl)

@[simp]
theorem inv_toLinearHomotopyEquiv {dM : Module.End R M} {dN : Module.End R N}
    (c : LinearContraction dM dN) : c.toLinearHomotopyEquiv.inv = c.incl := (rfl)

@[simp]
theorem homotopyInvHom_toLinearHomotopyEquiv {dM : Module.End R M} {dN : Module.End R N}
    (c : LinearContraction dM dN) : c.toLinearHomotopyEquiv.homotopyInvHom = -c.homotopy := (rfl)

@[simp]
theorem homotopyHomInv_toLinearHomotopyEquiv {dM : Module.End R M} {dN : Module.End R N}
    (c : LinearContraction dM dN) : c.toLinearHomotopyEquiv.homotopyHomInv = 0 := (rfl)

/-- A contraction with homogeneous inclusion, projection, and degree-`r` homotopy yields a
homogeneous chain-homotopy equivalence of homotopy degree `r`. -/
theorem isHomogeneous_toLinearHomotopyEquiv {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M]
    [SetLike σN N] [NegMemClass σM M] [ZeroMemClass σN N]
    {dM : Module.End R M} {dN : Module.End R N} (c : LinearContraction dM dN)
    {𝒜 : ι → σM} {ℬ : ι → σN} {r : ι}
    (hincl : LinearMap.IsHomogeneous c.incl ℬ 𝒜 0)
    (hproj : LinearMap.IsHomogeneous c.proj 𝒜 ℬ 0)
    (hh : LinearMap.IsHomogeneous c.homotopy 𝒜 𝒜 r) :
    c.toLinearHomotopyEquiv.IsHomogeneous 𝒜 ℬ r :=
  ⟨hproj, hincl, hh.neg, LinearMap.isHomogeneous_zero ℬ ℬ r⟩

end LinearContraction

end TauCeti
