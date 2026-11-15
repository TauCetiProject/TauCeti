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

`LinearHomotopyEquiv dM dN` packages a two-sided chain-homotopy equivalence between `(M, dM)` and
`(N, dN)` without assuming `d² = 0`, using the sign convention `d h + h d = g ∘ f - 1` matching
`TauCeti.AInfinityHom.Homotopy`.

## Main definitions

* `TauCeti.LinearHomotopyEquiv`, `TauCeti.LinearHomotopyEquiv.IsHomogeneous`.
* `TauCeti.LinearHomotopyEquiv.refl`, `symm`, `trans`, `ofLinearEquiv`, `ofHomotopy`.
* `TauCeti.LinearContraction.toLinearHomotopyEquiv`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Section 1.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 1.5.
-/

public section

universe uR uM uN uP

namespace TauCeti

variable {R : Type uR} {M : Type uM} {N : Type uN} {P : Type uP} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A two-sided chain-homotopy equivalence between `(M, dM)` and `(N, dN)` with sign convention
`d h + h d = g ∘ f - 1`. -/
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

variable {dM : Module.End R M} {dN : Module.End R N} {dP : Module.End R P}

@[simp] theorem dN_hom_apply (e : LinearHomotopyEquiv dM dN) (x : M) :
    dN (e.hom x) = e.hom (dM x) := LinearMap.congr_fun e.dN_comp_hom x
@[simp] theorem dM_inv_apply (e : LinearHomotopyEquiv dM dN) (y : N) :
    dM (e.inv y) = e.inv (dN y) := LinearMap.congr_fun e.dM_comp_inv y

/-- Express `inv ∘ hom` as `1 + dM ∘ homotopyInvHom + homotopyInvHom ∘ dM`. -/
theorem inv_comp_hom (e : LinearHomotopyEquiv dM dN) :
    e.inv ∘ₗ e.hom = LinearMap.id + (dM ∘ₗ e.homotopyInvHom + e.homotopyInvHom ∘ₗ dM) := by
  rw [e.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM, add_sub_cancel]
/-- Express `hom ∘ inv` as `1 + dN ∘ homotopyHomInv + homotopyHomInv ∘ dN`. -/
theorem hom_comp_inv (e : LinearHomotopyEquiv dM dN) :
    e.hom ∘ₗ e.inv = LinearMap.id + (dN ∘ₗ e.homotopyHomInv + e.homotopyHomInv ∘ₗ dN) := by
  rw [e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN, add_sub_cancel]

/-- Homogeneity of a chain-homotopy equivalence: `hom` and `inv` have degree zero and both
homotopies have degree `r`. -/
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

/-! ### Constructions and operations -/

/-- The identity chain-homotopy equivalence of `(M, dM)` with zero homotopies. -/
@[expose, simps -fullyApplied]
def refl (dM : Module.End R M) : LinearHomotopyEquiv dM dM where
  hom := LinearMap.id; inv := LinearMap.id; homotopyInvHom := 0; homotopyHomInv := 0
  dN_comp_hom := by simp
  dM_comp_inv := by simp
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by simp
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by simp

/-- The identity chain-homotopy equivalence is homogeneous of any homotopy degree `r`. -/
theorem isHomogeneous_refl {ι σM : Type*} [AddMonoid ι] [SetLike σM M] [ZeroMemClass σM M]
    (dM : Module.End R M) (𝒜 : ι → σM) (r : ι) : (refl dM).IsHomogeneous 𝒜 𝒜 r :=
  ⟨LinearMap.isHomogeneous_id 𝒜, LinearMap.isHomogeneous_id 𝒜,
    LinearMap.isHomogeneous_zero 𝒜 𝒜 r, LinearMap.isHomogeneous_zero 𝒜 𝒜 r⟩

/-- Swap the forward and inverse maps of a chain-homotopy equivalence. -/
@[expose, simps -fullyApplied]
def symm (e : LinearHomotopyEquiv dM dN) : LinearHomotopyEquiv dN dM where
  hom := e.inv; inv := e.hom; homotopyInvHom := e.homotopyHomInv; homotopyHomInv := e.homotopyInvHom
  dN_comp_hom := e.dM_comp_inv
  dM_comp_inv := e.dN_comp_hom
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM :=
    e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN :=
    e.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM

/-- Swapping forward and inverse maps preserves homogeneity. -/
theorem IsHomogeneous.symm {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    {e : LinearHomotopyEquiv dM dN} {𝒜 : ι → σM} {ℬ : ι → σN} {r : ι}
    (he : e.IsHomogeneous 𝒜 ℬ r) : e.symm.IsHomogeneous ℬ 𝒜 r :=
  ⟨he.inv, he.hom, he.homotopyHomInv, he.homotopyInvHom⟩

private theorem trans_homotopy {u : N →ₗ[R] M} {v : M →ₗ[R] N} {w : Module.End R N}
    {hM : Module.End R M} {hN : Module.End R N} (hu : dM ∘ₗ u = u ∘ₗ dN) (hv : dN ∘ₗ v = v ∘ₗ dM)
    (hhM : dM ∘ₗ hM + hM ∘ₗ dM = u ∘ₗ v - LinearMap.id)
    (hhN : dN ∘ₗ hN + hN ∘ₗ dN = w - LinearMap.id) :
    dM ∘ₗ (u ∘ₗ hN ∘ₗ v + hM) + (u ∘ₗ hN ∘ₗ v + hM) ∘ₗ dM = u ∘ₗ w ∘ₗ v - LinearMap.id := by
  have hconj : dM ∘ₗ (u ∘ₗ hN ∘ₗ v) + (u ∘ₗ hN ∘ₗ v) ∘ₗ dM = u ∘ₗ (dN ∘ₗ hN + hN ∘ₗ dN) ∘ₗ v := by
    rw [← LinearMap.comp_assoc, hu, LinearMap.add_comp, LinearMap.comp_add]
    simp only [LinearMap.comp_assoc, ← hv]
  rw [LinearMap.comp_add, LinearMap.add_comp, add_add_add_comm, hconj, hhN, hhM,
    LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp]; abel

/-- Compose two chain-homotopy equivalences. -/
@[expose, simps -fullyApplied]
def trans (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
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
    simpa only [LinearMap.comp_assoc] using trans_homotopy e₁.dM_comp_inv e₁.dN_comp_hom
      e₁.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM
      e₂.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by
    simpa only [LinearMap.comp_assoc] using trans_homotopy e₂.dN_comp_hom e₂.dM_comp_inv
      e₂.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN
      e₁.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN

/-- Composing two homogeneous chain-homotopy equivalences preserves homogeneity. -/
theorem IsHomogeneous.trans {ι σM σN σP : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    [SetLike σP P] [AddMemClass σM M] [AddMemClass σP P]
    {e₁ : LinearHomotopyEquiv dM dN} {e₂ : LinearHomotopyEquiv dN dP}
    {𝒜 : ι → σM} {ℬ : ι → σN} {𝒞 : ι → σP} {r : ι}
    (h₁ : e₁.IsHomogeneous 𝒜 ℬ r) (h₂ : e₂.IsHomogeneous ℬ 𝒞 r) :
    (e₁.trans e₂).IsHomogeneous 𝒜 𝒞 r :=
  ⟨add_zero (0 : ι) ▸ h₂.hom.comp h₁.hom, add_zero (0 : ι) ▸ h₁.inv.comp h₂.inv,
    (by simpa only [zero_add, add_zero] using h₁.inv.comp (h₂.homotopyInvHom.comp h₁.hom) :
      LinearMap.IsHomogeneous _ 𝒜 𝒜 r).add h₁.homotopyInvHom,
    (by simpa only [zero_add, add_zero] using h₂.hom.comp (h₁.homotopyHomInv.comp h₂.inv) :
      LinearMap.IsHomogeneous _ 𝒞 𝒞 r).add h₂.homotopyHomInv⟩

/-- A linear equivalence intertwining `dM` and `dN` gives a chain-homotopy equivalence with zero
homotopies. -/
@[expose, simps -fullyApplied]
def ofLinearEquiv (e : M ≃ₗ[R] N) (hd : dN ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ dM) :
    LinearHomotopyEquiv dM dN where
  hom := e.toLinearMap; inv := e.symm.toLinearMap; homotopyInvHom := 0; homotopyHomInv := 0
  dN_comp_hom := hd
  dM_comp_inv := LinearMap.ext fun y ↦ e.injective <| by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, e.apply_symm_apply] using
      (LinearMap.congr_fun hd (e.symm y)).symm
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by simp [e.symm_comp]
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by simp [e.comp_symm]

/-- A degree-zero linear equivalence intertwining the differentials yields a homogeneous
chain-homotopy equivalence of any homotopy degree `r`. -/
theorem isHomogeneous_ofLinearEquiv {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    [ZeroMemClass σM M] [ZeroMemClass σN N] {e : M ≃ₗ[R] N}
    (hd : dN ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ dM) {𝒜 : ι → σM} {ℬ : ι → σN}
    (he : LinearMap.IsHomogeneous e.toLinearMap 𝒜 ℬ 0)
    (he' : LinearMap.IsHomogeneous e.symm.toLinearMap ℬ 𝒜 0) (r : ι) :
    (ofLinearEquiv e hd).IsHomogeneous 𝒜 ℬ r :=
  ⟨he, he', LinearMap.isHomogeneous_zero 𝒜 𝒜 r, LinearMap.isHomogeneous_zero ℬ ℬ r⟩

/-- Replace `e.hom` by a homotopic chain map `f'` satisfying `e.hom - f' = dN ∘ s + s ∘ dM`. -/
@[expose, simps -fullyApplied]
def ofHomotopy (e : LinearHomotopyEquiv dM dN) {f' : M →ₗ[R] N} (hf' : dN ∘ₗ f' = f' ∘ₗ dM)
    (s : M →ₗ[R] N) (hs : e.hom - f' = dN ∘ₗ s + s ∘ₗ dM) : LinearHomotopyEquiv dM dN where
  hom := f'; inv := e.inv
  homotopyInvHom := e.homotopyInvHom - e.inv ∘ₗ s
  homotopyHomInv := e.homotopyHomInv - s ∘ₗ e.inv
  dN_comp_hom := hf'; dM_comp_inv := e.dM_comp_inv
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by
    have h₁ : dM ∘ₗ (e.inv ∘ₗ s) + (e.inv ∘ₗ s) ∘ₗ dM = e.inv ∘ₗ (e.hom - f') := by
      rw [← LinearMap.comp_assoc, e.dM_comp_inv, LinearMap.comp_assoc, LinearMap.comp_assoc,
        ← LinearMap.comp_add, ← hs]
    rw [LinearMap.comp_sub, LinearMap.sub_comp, sub_add_sub_comm,
      e.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM, h₁, LinearMap.comp_sub]; abel
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by
    have h₂ : dN ∘ₗ (s ∘ₗ e.inv) + (s ∘ₗ e.inv) ∘ₗ dN = (e.hom - f') ∘ₗ e.inv := by
      rw [LinearMap.comp_assoc, e.dM_comp_inv.symm, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
        ← LinearMap.add_comp, ← hs]
    rw [LinearMap.comp_sub, LinearMap.sub_comp, sub_add_sub_comm,
      e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN, h₂, LinearMap.sub_comp]; abel

/-- Transporting the forward map along a degree-`r` chain homotopy preserves homogeneity. -/
theorem IsHomogeneous.ofHomotopy {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    [AddMemClass σM M] [NegMemClass σM M] [AddMemClass σN N] [NegMemClass σN N]
    {e : LinearHomotopyEquiv dM dN} {𝒜 : ι → σM} {ℬ : ι → σN} {r : ι}
    (he : e.IsHomogeneous 𝒜 ℬ r) {f' : M →ₗ[R] N} (hf' : dN ∘ₗ f' = f' ∘ₗ dM)
    (hf'₀ : LinearMap.IsHomogeneous f' 𝒜 ℬ 0) {s : M →ₗ[R] N}
    (hs₀ : LinearMap.IsHomogeneous s 𝒜 ℬ r) (hs : e.hom - f' = dN ∘ₗ s + s ∘ₗ dM) :
    (e.ofHomotopy hf' s hs).IsHomogeneous 𝒜 ℬ r :=
  ⟨hf'₀, he.inv, he.homotopyInvHom.sub (add_zero r ▸ he.inv.comp hs₀),
    he.homotopyHomInv.sub (zero_add r ▸ hs₀.comp he.inv)⟩
end LinearHomotopyEquiv

namespace LinearContraction
variable {dM : Module.End R M} {dN : Module.End R N} (c : LinearContraction dM dN)

/-- View a contraction as a chain-homotopy equivalence with `hom = proj`, `inv = incl`,
`homotopyInvHom = -homotopy`, and `homotopyHomInv = 0`. -/
@[expose, simps -fullyApplied]
def toLinearHomotopyEquiv : LinearHomotopyEquiv dM dN where
  hom := c.proj; inv := c.incl; homotopyInvHom := -c.homotopy; homotopyHomInv := 0
  dN_comp_hom := c.proj_comp_dM.symm; dM_comp_inv := c.dM_comp_incl
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by
    rw [LinearMap.comp_neg, LinearMap.neg_comp, ← neg_add,
      c.dM_comp_homotopy_add_homotopy_comp_dM, neg_sub]
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by simp [c.proj_comp_incl]

/-- A contraction with homogeneous data yields a homogeneous chain-homotopy equivalence. -/
theorem isHomogeneous_toLinearHomotopyEquiv {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M]
    [SetLike σN N] [NegMemClass σM M] [ZeroMemClass σN N]
    {𝒜 : ι → σM} {ℬ : ι → σN} {r : ι} (hincl : LinearMap.IsHomogeneous c.incl ℬ 𝒜 0)
    (hproj : LinearMap.IsHomogeneous c.proj 𝒜 ℬ 0)
    (hh : LinearMap.IsHomogeneous c.homotopy 𝒜 𝒜 r) :
    c.toLinearHomotopyEquiv.IsHomogeneous 𝒜 ℬ r :=
  ⟨hproj, hincl, hh.neg, LinearMap.isHomogeneous_zero ℬ ℬ r⟩
end LinearContraction

end TauCeti
