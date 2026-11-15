/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear.Homology

/-!
# Homotopy equivalences of modules with an endomorphism

A *linear homotopy equivalence* between a module `M` with an endomorphism `dM` and a module `N`
with an endomorphism `dN` consists of chain maps `hom : M →ₗ[R] N` and `inv : N →ₗ[R] M` together
with homotopies `homotopyHomInv : M →ₗ[R] M` and `homotopyInvHom : N →ₗ[R] N` satisfying

`dM ∘ homotopyHomInv + homotopyHomInv ∘ dM = 1 - inv ∘ hom`,
`dN ∘ homotopyInvHom + homotopyInvHom ∘ dN = 1 - hom ∘ inv`.

This is the symmetric counterpart of `TauCeti.LinearContraction`, in which neither composite need
be the identity on the nose; every `LinearContraction` gives a `LinearHomotopyEquiv` with zero
homotopy on the retract (`TauCeti.LinearContraction.toLinearHomotopyEquiv`).  As in
`LinearContraction`, nothing in the data forces `dM` or `dN` to square to zero, and when they do
the forward and backward maps induce mutually inverse isomorphisms on concrete homology
(`TauCeti.LinearHomotopyEquiv.homologyEquiv`).

Two algebraic constructions drive the lifting of `A∞` morphisms and transformations along homotopy
equivalences:

* **Simultaneous obstruction solving** (`TauCeti.LinearHomotopyEquiv.obstructionLift` and
  `TauCeti.LinearHomotopyEquiv.obstructionHomotopy`): given an endomorphism `b` of a module `W`, a
  scalar `ε : R`, and maps `Φ : W →ₗ[R] M` and `Ψ : W →ₗ[R] N` with `dM ∘ Φ + ε • (Φ ∘ b) = 0`
  and `dN ∘ Ψ - ε • (Ψ ∘ b) = hom ∘ Φ`, explicit linear combinations of `Φ` and `Ψ` produce
  `γ : W →ₗ[R] M` and `η : W →ₗ[R] N` solving `dM ∘ γ - ε • (γ ∘ b) = Φ` and
  `hom ∘ γ + (dN ∘ η + ε • (η ∘ b)) = Ψ`, without assuming `b² = 0` or `ε² = 1`.
* **Homotopy inverses of graded quasi-isomorphisms over a division ring**
  (`TauCeti.InternalGrading.linearHomotopyEquivOfBijectiveHomologyMap`): over a division ring, any
  degree-zero chain map between internally `ℤ`-graded modules with square-zero degree-one
  differentials that induces a bijection on homology extends to a graded `LinearHomotopyEquiv` with
  that exact forward map, constructed by transporting the homology isomorphism across
  `TauCeti.InternalGrading.homologyContraction`.

## Main definitions

* `TauCeti.LinearHomotopyEquiv`: homotopy equivalence data between `(M, dM)` and `(N, dN)`.
* `TauCeti.LinearContraction.toLinearHomotopyEquiv`: a contraction viewed as a homotopy
  equivalence.
* `TauCeti.LinearHomotopyEquiv.IsGraded`: compatibility of a homotopy equivalence with gradings.
* `TauCeti.LinearHomotopyEquiv.obstructionLift` and
  `TauCeti.LinearHomotopyEquiv.obstructionHomotopy`: explicit solutions of coupled homological
  obstruction equations along a homotopy equivalence.
* `TauCeti.InternalGrading.linearHomotopyEquivOfBijectiveHomologyMap`: graded homotopy equivalence
  extending a quasi-isomorphism over a division ring.

## Main results

* `LinearMap.homologyMap_eq_of_sub_eq_add`: chain-homotopic maps induce the same map on homology.
* `TauCeti.LinearHomotopyEquiv.homologyEquiv`: the induced linear equivalence on homology.
* `TauCeti.LinearHomotopyEquiv.dM_comp_obstructionLift_sub` and
  `TauCeti.LinearHomotopyEquiv.hom_comp_obstructionLift_add`: the obstruction equations satisfied
  by `obstructionLift` and `obstructionHomotopy`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Section 1.4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.7.
-/

public section

universe uR uM uN uP uW

namespace LinearMap

variable {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  {dM : M →ₗ[S] M} {dN : N →ₗ[S] N}

/-- Chain-homotopic linear maps between modules with square-zero endomorphisms induce the same map
on concrete homology. -/
theorem homologyMap_eq_of_sub_eq_add {f g h : M →ₗ[S] N} (hdM : dM ∘ₗ dM = 0)
    (hdN : dN ∘ₗ dN = 0) (hf : f ∘ₗ dM = dN ∘ₗ f) (hg : g ∘ₗ dM = dN ∘ₗ g)
    (hh : f - g = dN ∘ₗ h + h ∘ₗ dM) :
    dM.homologyMap f hdM hdN hf = dM.homologyMap g hdM hdN hg := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := dM.homologyπ_surjective hdM c
  rw [ ← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.homologyMap_sub,
    dM.homologyπ_apply, LinearMap.homologyMap_mk, ← dN.homologyπ_apply,
    dN.homologyπ_eq_zero_iff]
  refine ⟨h z, ?_⟩
  have hz : dM z = 0 := z.2
  have key := LinearMap.congr_fun hh z
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero,
    add_zero] at key
  exact key.symm

end LinearMap

namespace TauCeti

section Semiring

variable {R : Type uR} {M : Type uM} {N : Type uN} {P : Type uP} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A homotopy equivalence between modules with endomorphisms `dM` and `dN`: mutually homotopy
inverse chain maps `hom` and `inv` together with contracting homotopies on both sides. -/
@[ext]
structure LinearHomotopyEquiv (dM : Module.End R M) (dN : Module.End R N) where
  /-- The forward chain map. -/
  hom : M →ₗ[R] N
  /-- The backward chain map. -/
  inv : N →ₗ[R] M
  /-- The homotopy from `1` to `inv ∘ hom` on `M`. -/
  homotopyHomInv : Module.End R M
  /-- The homotopy from `1` to `hom ∘ inv` on `N`. -/
  homotopyInvHom : Module.End R N
  /-- The forward map intertwines the endomorphisms. -/
  dN_comp_hom : dN ∘ₗ hom = hom ∘ₗ dM
  /-- The backward map intertwines the endomorphisms. -/
  dM_comp_inv : dM ∘ₗ inv = inv ∘ₗ dN
  /-- The homotopy relation on `M`. -/
  dM_comp_homotopyHomInv_add :
    dM ∘ₗ homotopyHomInv + homotopyHomInv ∘ₗ dM = LinearMap.id - inv ∘ₗ hom
  /-- The homotopy relation on `N`. -/
  dN_comp_homotopyInvHom_add :
    dN ∘ₗ homotopyInvHom + homotopyInvHom ∘ₗ dN = LinearMap.id - hom ∘ₗ inv

namespace LinearHomotopyEquiv

variable {dM : Module.End R M} {dN : Module.End R N} {dP : Module.End R P}

/-- `hom ∘ dM = dN ∘ hom`, oriented for `LinearMap.homologyMap`. -/
theorem hom_comp_dM (e : LinearHomotopyEquiv dM dN) : e.hom ∘ₗ dM = dN ∘ₗ e.hom :=
  e.dN_comp_hom.symm

/-- `inv ∘ dN = dM ∘ inv`, oriented for `LinearMap.homologyMap`. -/
theorem inv_comp_dN (e : LinearHomotopyEquiv dM dN) : e.inv ∘ₗ dN = dM ∘ₗ e.inv :=
  e.dM_comp_inv.symm

/-- The forward map `hom` commutes with the differentials on elements. -/
@[simp]
theorem dN_hom_apply (e : LinearHomotopyEquiv dM dN) (x : M) : dN (e.hom x) = e.hom (dM x) :=
  LinearMap.congr_fun e.dN_comp_hom x

/-- The backward map `inv` commutes with the differentials on elements. -/
@[simp]
theorem dM_inv_apply (e : LinearHomotopyEquiv dM dN) (y : N) : dM (e.inv y) = e.inv (dN y) :=
  LinearMap.congr_fun e.dM_comp_inv y

/-- The identity homotopy equivalence of `(M, dM)`, with zero homotopies. -/
def refl (dM : Module.End R M) : LinearHomotopyEquiv dM dM where
  hom := LinearMap.id
  inv := LinearMap.id
  homotopyHomInv := 0
  homotopyInvHom := 0
  dN_comp_hom := by simp
  dM_comp_inv := by simp
  dM_comp_homotopyHomInv_add := by simp
  dN_comp_homotopyInvHom_add := by simp

/-- The forward map of `refl dM` is the identity. -/
@[simp] theorem refl_hom (dM : Module.End R M) : (refl dM).hom = LinearMap.id := (rfl)

/-- The backward map of `refl dM` is the identity. -/
@[simp] theorem refl_inv (dM : Module.End R M) : (refl dM).inv = LinearMap.id := (rfl)

/-- The source homotopy of `refl dM` is zero. -/
@[simp] theorem refl_homotopyHomInv (dM : Module.End R M) : (refl dM).homotopyHomInv = 0 := (rfl)

/-- The target homotopy of `refl dM` is zero. -/
@[simp] theorem refl_homotopyInvHom (dM : Module.End R M) : (refl dM).homotopyInvHom = 0 := (rfl)

/-- Reversing the forward and backward maps of a homotopy equivalence. -/
def symm (e : LinearHomotopyEquiv dM dN) : LinearHomotopyEquiv dN dM where
  hom := e.inv
  inv := e.hom
  homotopyHomInv := e.homotopyInvHom
  homotopyInvHom := e.homotopyHomInv
  dN_comp_hom := e.dM_comp_inv
  dM_comp_inv := e.dN_comp_hom
  dM_comp_homotopyHomInv_add := e.dN_comp_homotopyInvHom_add
  dN_comp_homotopyInvHom_add := e.dM_comp_homotopyHomInv_add

/-- The forward map of `e.symm` is `e.inv`. -/
@[simp] theorem symm_hom (e : LinearHomotopyEquiv dM dN) : e.symm.hom = e.inv := (rfl)

/-- The backward map of `e.symm` is `e.hom`. -/
@[simp] theorem symm_inv (e : LinearHomotopyEquiv dM dN) : e.symm.inv = e.hom := (rfl)

/-- The source homotopy of `e.symm` is `e.homotopyInvHom`. -/
@[simp] theorem symm_homotopyHomInv (e : LinearHomotopyEquiv dM dN) :
    e.symm.homotopyHomInv = e.homotopyInvHom := (rfl)

/-- The target homotopy of `e.symm` is `e.homotopyHomInv`. -/
@[simp] theorem symm_homotopyInvHom (e : LinearHomotopyEquiv dM dN) :
    e.symm.homotopyInvHom = e.homotopyHomInv := (rfl)

/-- Reversing `symm` recovers the original homotopy equivalence. -/
@[simp] theorem symm_symm (e : LinearHomotopyEquiv dM dN) : e.symm.symm = e := (rfl)

/-- Auxiliary identity for composing the homotopies of two homotopy equivalences. -/
private theorem comp_homotopy_eq {f₁ : M →ₗ[R] N} {g₁ : N →ₗ[R] M} {f₂ : N →ₗ[R] P}
    {g₂ : P →ₗ[R] N} {hM : Module.End R M} {kN : Module.End R N}
    (hf₁ : dN ∘ₗ f₁ = f₁ ∘ₗ dM) (hg₁ : dM ∘ₗ g₁ = g₁ ∘ₗ dN)
    (hhM : dM ∘ₗ hM + hM ∘ₗ dM = LinearMap.id - g₁ ∘ₗ f₁)
    (hkN : dN ∘ₗ kN + kN ∘ₗ dN = LinearMap.id - g₂ ∘ₗ f₂) :
    dM ∘ₗ (hM + g₁ ∘ₗ kN ∘ₗ f₁) + (hM + g₁ ∘ₗ kN ∘ₗ f₁) ∘ₗ dM =
      LinearMap.id - (g₁ ∘ₗ g₂) ∘ₗ (f₂ ∘ₗ f₁) := by
  have hg₁d : dM ∘ₗ (g₁ ∘ₗ kN ∘ₗ f₁) = g₁ ∘ₗ (dN ∘ₗ kN) ∘ₗ f₁ := by
    rw [← LinearMap.comp_assoc, hg₁]
    simp only [LinearMap.comp_assoc]
  have hdf₁ : (g₁ ∘ₗ kN ∘ₗ f₁) ∘ₗ dM = g₁ ∘ₗ (kN ∘ₗ dN) ∘ₗ f₁ := by
    simp only [LinearMap.comp_assoc, ← hf₁]
  have hmid : g₁ ∘ₗ (dN ∘ₗ kN) ∘ₗ f₁ + g₁ ∘ₗ (kN ∘ₗ dN) ∘ₗ f₁ =
      g₁ ∘ₗ f₁ - (g₁ ∘ₗ g₂) ∘ₗ (f₂ ∘ₗ f₁) := by
    rw [← LinearMap.comp_add, ← LinearMap.add_comp, hkN, LinearMap.sub_comp, LinearMap.comp_sub,
      LinearMap.id_comp]
    simp only [LinearMap.comp_assoc]
  calc
    dM ∘ₗ (hM + g₁ ∘ₗ kN ∘ₗ f₁) + (hM + g₁ ∘ₗ kN ∘ₗ f₁) ∘ₗ dM
      = (dM ∘ₗ hM + hM ∘ₗ dM) + (dM ∘ₗ (g₁ ∘ₗ kN ∘ₗ f₁) + (g₁ ∘ₗ kN ∘ₗ f₁) ∘ₗ dM) := by
        rw [LinearMap.comp_add, LinearMap.add_comp]
        abel
    _ = (LinearMap.id - g₁ ∘ₗ f₁) + (g₁ ∘ₗ f₁ - (g₁ ∘ₗ g₂) ∘ₗ (f₂ ∘ₗ f₁)) := by
        rw [hhM, hg₁d, hdf₁, hmid]
    _ = LinearMap.id - (g₁ ∘ₗ g₂) ∘ₗ (f₂ ∘ₗ f₁) := by abel

/-- Composition of homotopy equivalences. -/
def trans (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
    LinearHomotopyEquiv dM dP where
  hom := e₂.hom ∘ₗ e₁.hom
  inv := e₁.inv ∘ₗ e₂.inv
  homotopyHomInv := e₁.homotopyHomInv + e₁.inv ∘ₗ e₂.homotopyHomInv ∘ₗ e₁.hom
  homotopyInvHom := e₂.homotopyInvHom + e₂.hom ∘ₗ e₁.homotopyInvHom ∘ₗ e₂.inv
  dN_comp_hom := by
    rw [← LinearMap.comp_assoc, e₂.dN_comp_hom, LinearMap.comp_assoc, e₁.dN_comp_hom,
      LinearMap.comp_assoc]
  dM_comp_inv := by
    rw [← LinearMap.comp_assoc, e₁.dM_comp_inv, LinearMap.comp_assoc, e₂.dM_comp_inv,
      LinearMap.comp_assoc]
  dM_comp_homotopyHomInv_add :=
    comp_homotopy_eq e₁.dN_comp_hom e₁.dM_comp_inv e₁.dM_comp_homotopyHomInv_add
      e₂.dM_comp_homotopyHomInv_add
  dN_comp_homotopyInvHom_add :=
    comp_homotopy_eq e₂.dM_comp_inv e₂.dN_comp_hom e₂.dN_comp_homotopyInvHom_add
      e₁.dN_comp_homotopyInvHom_add

/-- The forward map of `e₁.trans e₂` is `e₂.hom ∘ₗ e₁.hom`. -/
@[simp] theorem trans_hom (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).hom = e₂.hom ∘ₗ e₁.hom := (rfl)

/-- The backward map of `e₁.trans e₂` is `e₁.inv ∘ₗ e₂.inv`. -/
@[simp] theorem trans_inv (e₁ : LinearHomotopyEquiv dM dN) (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).inv = e₁.inv ∘ₗ e₂.inv := (rfl)

/-- The source homotopy of `e₁.trans e₂`. -/
@[simp] theorem trans_homotopyHomInv (e₁ : LinearHomotopyEquiv dM dN)
    (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).homotopyHomInv = e₁.homotopyHomInv + e₁.inv ∘ₗ e₂.homotopyHomInv ∘ₗ e₁.hom :=
  (rfl)

/-- The target homotopy of `e₁.trans e₂`. -/
@[simp] theorem trans_homotopyInvHom (e₁ : LinearHomotopyEquiv dM dN)
    (e₂ : LinearHomotopyEquiv dN dP) :
    (e₁.trans e₂).homotopyInvHom = e₂.homotopyInvHom + e₂.hom ∘ₗ e₁.homotopyInvHom ∘ₗ e₂.inv :=
  (rfl)

/-- A chain-map linear equivalence is a homotopy equivalence with zero homotopies. -/
def ofLinearEquiv (e : M ≃ₗ[R] N) (he : dN ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ dM) :
    LinearHomotopyEquiv dM dN where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  homotopyHomInv := 0
  homotopyInvHom := 0
  dN_comp_hom := he
  dM_comp_inv := LinearMap.ext fun y ↦ e.injective <| by
    have key := LinearMap.congr_fun he (e.symm y)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      key.symm
  dM_comp_homotopyHomInv_add := by simp
  dN_comp_homotopyInvHom_add := by simp

/-- The forward map of `ofLinearEquiv e he` is `e`. -/
@[simp] theorem ofLinearEquiv_hom (e : M ≃ₗ[R] N)
    (he : dN ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ dM) :
    (ofLinearEquiv e he).hom = e.toLinearMap := (rfl)

/-- The backward map of `ofLinearEquiv e he` is `e.symm`. -/
@[simp] theorem ofLinearEquiv_inv (e : M ≃ₗ[R] N)
    (he : dN ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ dM) :
    (ofLinearEquiv e he).inv = e.symm.toLinearMap := (rfl)

/-- Compatibility of a `LinearHomotopyEquiv` with gradings `𝒜` and `ℬ` when the differentials
have degree `q`: `hom` and `inv` have degree zero and both homotopies have degree `-q`. -/
structure IsGraded {ι σM σN : Type*} [AddGroup ι] [SetLike σM M] [SetLike σN N]
    (𝒜 : ι → σM) (ℬ : ι → σN) (q : ι) (e : LinearHomotopyEquiv dM dN) : Prop where
  /-- The forward map preserves degrees. -/
  hom : LinearMap.IsHomogeneous e.hom 𝒜 ℬ 0
  /-- The backward map preserves degrees. -/
  inv : LinearMap.IsHomogeneous e.inv ℬ 𝒜 0
  /-- The homotopy on `M` has degree `-q`. -/
  homotopyHomInv : LinearMap.IsHomogeneous e.homotopyHomInv 𝒜 𝒜 (-q)
  /-- The homotopy on `N` has degree `-q`. -/
  homotopyInvHom : LinearMap.IsHomogeneous e.homotopyInvHom ℬ ℬ (-q)

namespace IsGraded

variable {ι σM σN σP : Type*} [AddGroup ι] [SetLike σM M] [SetLike σN N] [SetLike σP P]
  {𝒜 : ι → σM} {ℬ : ι → σN} {𝒞 : ι → σP} {q : ι}

/-- The identity homotopy equivalence is graded. -/
theorem refl [ZeroMemClass σM M] (𝒜 : ι → σM) (q : ι) :
    (LinearHomotopyEquiv.refl dM).IsGraded 𝒜 𝒜 q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [refl_hom]; exact LinearMap.isHomogeneous_id 𝒜
  · rw [refl_inv]; exact LinearMap.isHomogeneous_id 𝒜
  · rw [refl_homotopyHomInv]; exact LinearMap.isHomogeneous_zero 𝒜 𝒜 (-q)
  · rw [refl_homotopyInvHom]; exact LinearMap.isHomogeneous_zero 𝒜 𝒜 (-q)

/-- Reversing a graded homotopy equivalence preserves its grading compatibility. -/
theorem symm {e : LinearHomotopyEquiv dM dN} (he : e.IsGraded 𝒜 ℬ q) :
    e.symm.IsGraded ℬ 𝒜 q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [symm_hom]; exact he.inv
  · rw [symm_inv]; exact he.hom
  · rw [symm_homotopyHomInv]; exact he.homotopyInvHom
  · rw [symm_homotopyInvHom]; exact he.homotopyHomInv

/-- Composing graded homotopy equivalences preserves grading compatibility. -/
theorem trans [AddMemClass σM M] [AddMemClass σP P] {e₁ : LinearHomotopyEquiv dM dN}
    {e₂ : LinearHomotopyEquiv dN dP} (he₁ : e₁.IsGraded 𝒜 ℬ q) (he₂ : e₂.IsGraded ℬ 𝒞 q) :
    (e₁.trans e₂).IsGraded 𝒜 𝒞 q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [trans_hom]; simpa only [zero_add] using he₂.hom.comp he₁.hom
  · rw [trans_inv]; simpa only [zero_add] using he₁.inv.comp he₂.inv
  · rw [trans_homotopyHomInv]
    exact he₁.homotopyHomInv.add <| by
      simpa only [zero_add, add_zero] using he₁.inv.comp (he₂.homotopyHomInv.comp he₁.hom)
  · rw [trans_homotopyInvHom]
    exact he₂.homotopyInvHom.add <| by
      simpa only [zero_add, add_zero] using he₂.hom.comp (he₁.homotopyInvHom.comp he₂.inv)

end IsGraded

end LinearHomotopyEquiv

/-- A contraction of `(M, dM)` onto `(N, dN)` viewed as a homotopy equivalence, with `proj` as
forward map, `incl` as backward map, and zero homotopy on the retract `N`. -/
def LinearContraction.toLinearHomotopyEquiv {dM : Module.End R M} {dN : Module.End R N}
    (c : LinearContraction dM dN) : LinearHomotopyEquiv dM dN where
  hom := c.proj
  inv := c.incl
  homotopyHomInv := c.homotopy
  homotopyInvHom := 0
  dN_comp_hom := c.proj_comp_dM.symm
  dM_comp_inv := c.dM_comp_incl
  dM_comp_homotopyHomInv_add := c.dM_comp_homotopy_add_homotopy_comp_dM
  dN_comp_homotopyInvHom_add := by simp

/-- The forward map of `c.toLinearHomotopyEquiv` is the projection `c.proj`. -/
@[simp]
theorem LinearContraction.toLinearHomotopyEquiv_hom {dM : Module.End R M} {dN : Module.End R N}
    (c : LinearContraction dM dN) : c.toLinearHomotopyEquiv.hom = c.proj := (rfl)

/-- The backward map of `c.toLinearHomotopyEquiv` is the inclusion `c.incl`. -/
@[simp]
theorem LinearContraction.toLinearHomotopyEquiv_inv {dM : Module.End R M} {dN : Module.End R N}
    (c : LinearContraction dM dN) : c.toLinearHomotopyEquiv.inv = c.incl := (rfl)

/-- The source homotopy of `c.toLinearHomotopyEquiv` is `c.homotopy`. -/
@[simp]
theorem LinearContraction.toLinearHomotopyEquiv_homotopyHomInv {dM : Module.End R M}
    {dN : Module.End R N} (c : LinearContraction dM dN) :
    c.toLinearHomotopyEquiv.homotopyHomInv = c.homotopy := (rfl)

/-- The target homotopy of `c.toLinearHomotopyEquiv` vanishes. -/
@[simp]
theorem LinearContraction.toLinearHomotopyEquiv_homotopyInvHom {dM : Module.End R M}
    {dN : Module.End R N} (c : LinearContraction dM dN) :
    c.toLinearHomotopyEquiv.homotopyInvHom = 0 := (rfl)

/-- A contraction with homogeneous components gives a graded homotopy equivalence. -/
theorem LinearContraction.isGraded_toLinearHomotopyEquiv {ι σM σN : Type*} [AddGroup ι]
    [SetLike σM M] [SetLike σN N] [ZeroMemClass σN N] {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι}
    {dM : Module.End R M} {dN : Module.End R N} (c : LinearContraction dM dN)
    (hincl : LinearMap.IsHomogeneous c.incl ℬ 𝒜 0)
    (hproj : LinearMap.IsHomogeneous c.proj 𝒜 ℬ 0)
    (hhom : LinearMap.IsHomogeneous c.homotopy 𝒜 𝒜 (-q)) :
    c.toLinearHomotopyEquiv.IsGraded 𝒜 ℬ q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toLinearHomotopyEquiv_hom]; exact hproj
  · rw [toLinearHomotopyEquiv_inv]; exact hincl
  · rw [toLinearHomotopyEquiv_homotopyHomInv]; exact hhom
  · rw [toLinearHomotopyEquiv_homotopyInvHom]; exact LinearMap.isHomogeneous_zero ℬ ℬ (-q)

end Semiring

/-! ### Induced isomorphism on homology -/

section Ring

variable {R : Type uR} {M : Type uM} {N : Type uN} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N}

namespace LinearHomotopyEquiv

/-- A homotopy equivalence between square-zero endomorphisms induces a linear equivalence on
concrete homology. -/
noncomputable def homologyEquiv (e : LinearHomotopyEquiv dM dN)
    (hdM : dM ∘ₗ dM = 0) (hdN : dN ∘ₗ dN = 0) :
    dM.homology hdM ≃ₗ[R] dN.homology hdN :=
  LinearEquiv.ofLinearMap
    (dM.homologyMap e.hom hdM hdN e.hom_comp_dM)
    (dN.homologyMap e.inv hdN hdM e.inv_comp_dN)
    (by
      rw [LinearMap.homologyMap_comp_homologyMap, ← dN.homologyMap_id hdN]
      exact (dN.homologyMap_eq_of_sub_eq_add hdN hdN (by simp) _
        e.dN_comp_homotopyInvHom_add.symm).symm)
    (by
      rw [LinearMap.homologyMap_comp_homologyMap, ← dM.homologyMap_id hdM]
      exact (dM.homologyMap_eq_of_sub_eq_add hdM hdM (by simp) _
        e.dM_comp_homotopyHomInv_add.symm).symm)

/-- The forward linear map of `e.homologyEquiv` is `homologyMap e.hom`. -/
@[simp]
theorem coe_homologyEquiv (e : LinearHomotopyEquiv dM dN) (hdM : dM ∘ₗ dM = 0)
    (hdN : dN ∘ₗ dN = 0) :
    (e.homologyEquiv hdM hdN : dM.homology hdM →ₗ[R] dN.homology hdN) =
      dM.homologyMap e.hom hdM hdN e.hom_comp_dM := (rfl)

/-- The inverse linear map of `e.homologyEquiv` is `homologyMap e.inv`. -/
@[simp]
theorem coe_homologyEquiv_symm (e : LinearHomotopyEquiv dM dN) (hdM : dM ∘ₗ dM = 0)
    (hdN : dN ∘ₗ dN = 0) :
    ((e.homologyEquiv hdM hdN).symm : dN.homology hdN →ₗ[R] dM.homology hdM) =
      dN.homologyMap e.inv hdN hdM e.inv_comp_dN := (rfl)

/-- The forward map of a homotopy equivalence between square-zero endomorphisms induces a bijection
on concrete homology. -/
theorem bijective_homologyMap (e : LinearHomotopyEquiv dM dN) (hdM : dM ∘ₗ dM = 0)
    (hdN : dN ∘ₗ dN = 0) :
    Function.Bijective (dM.homologyMap e.hom hdM hdN e.hom_comp_dM) :=
  (e.homologyEquiv hdM hdN).bijective

end LinearHomotopyEquiv

end Ring

/-! ### Solving coupled homological obstruction equations -/

section ObstructionDefs

variable {R : Type uR} {M : Type uM} {N : Type uN} {W : Type uW} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommMonoid W] [Module R W]
  {dM : Module.End R M} {dN : Module.End R N}

namespace LinearHomotopyEquiv

/-- Preliminary lift `γ₀ = inv ∘ Ψ + homotopyHomInv ∘ Φ` for coupled homological obstructions. -/
private def obstructionInitialLift (e : LinearHomotopyEquiv dM dN)
    (Φ : W →ₗ[R] M) (Ψ : W →ₗ[R] N) : W →ₗ[R] M :=
  e.inv ∘ₗ Ψ + e.homotopyHomInv ∘ₗ Φ

/-- Residual discrepancy `Ξ = Ψ - hom ∘ γ₀` in the target after the initial lift. -/
private def obstructionResidual (e : LinearHomotopyEquiv dM dN)
    (Φ : W →ₗ[R] M) (Ψ : W →ₗ[R] N) : W →ₗ[R] N :=
  Ψ - e.hom ∘ₗ e.obstructionInitialLift Φ Ψ

/-- Explicit lift `γ : W →ₗ[R] M` solving the coupled homological obstruction equations
`dM ∘ γ - ε • (γ ∘ b) = Φ` and `hom ∘ γ + (dN ∘ η + ε • (η ∘ b)) = Ψ` along a homotopy equivalence
`e`, given `dM ∘ Φ + ε • (Φ ∘ b) = 0` and `dN ∘ Ψ - ε • (Ψ ∘ b) = hom ∘ Φ`. -/
def obstructionLift (e : LinearHomotopyEquiv dM dN) (Φ : W →ₗ[R] M) (Ψ : W →ₗ[R] N) :
    W →ₗ[R] M :=
  e.obstructionInitialLift Φ Ψ + e.inv ∘ₗ e.obstructionResidual Φ Ψ

/-- Explicit homotopy correction `η : W →ₗ[R] N` accompanying `obstructionLift` in the coupled
homological obstruction equations `hom ∘ γ + (dN ∘ η + ε • (η ∘ b)) = Ψ`. -/
def obstructionHomotopy (e : LinearHomotopyEquiv dM dN) (Φ : W →ₗ[R] M) (Ψ : W →ₗ[R] N) :
    W →ₗ[R] N :=
  e.homotopyInvHom ∘ₗ e.obstructionResidual Φ Ψ

/-- `obstructionLift` commutes with precomposition on the source `W`. -/
theorem obstructionLift_comp {W' : Type*} [AddCommMonoid W'] [Module R W']
    (e : LinearHomotopyEquiv dM dN) (Φ : W →ₗ[R] M) (Ψ : W →ₗ[R] N) (π : W' →ₗ[R] W) :
    e.obstructionLift Φ Ψ ∘ₗ π = e.obstructionLift (Φ ∘ₗ π) (Ψ ∘ₗ π) := by
  simp only [obstructionLift, obstructionResidual, obstructionInitialLift, LinearMap.add_comp,
    LinearMap.sub_comp, LinearMap.comp_assoc]

/-- `obstructionHomotopy` commutes with precomposition on the source `W`. -/
theorem obstructionHomotopy_comp {W' : Type*} [AddCommMonoid W'] [Module R W']
    (e : LinearHomotopyEquiv dM dN) (Φ : W →ₗ[R] M) (Ψ : W →ₗ[R] N) (π : W' →ₗ[R] W) :
    e.obstructionHomotopy Φ Ψ ∘ₗ π = e.obstructionHomotopy (Φ ∘ₗ π) (Ψ ∘ₗ π) := by
  simp only [obstructionHomotopy, obstructionResidual, obstructionInitialLift, LinearMap.add_comp,
    LinearMap.sub_comp, LinearMap.comp_assoc]

private theorem isHomogeneous_obstructionInitialLift {ι σM σN σW : Type*} [AddGroup ι]
    [SetLike σM M] [SetLike σN N] [SetLike σW W] [AddMemClass σM M]
    {𝒜 : ι → σM} {ℬ : ι → σN} {𝒲 : ι → σW} {q r : ι} {e : LinearHomotopyEquiv dM dN}
    (he : e.IsGraded 𝒜 ℬ q) {Φ : W →ₗ[R] M} {Ψ : W →ₗ[R] N}
    (hΦ : LinearMap.IsHomogeneous Φ 𝒲 𝒜 (r + q)) (hΨ : LinearMap.IsHomogeneous Ψ 𝒲 ℬ r) :
    LinearMap.IsHomogeneous (e.obstructionInitialLift Φ Ψ) 𝒲 𝒜 r := by
  rw [obstructionInitialLift]
  exact LinearMap.IsHomogeneous.add (by simpa only [add_zero] using he.inv.comp hΨ)
    (by simpa only [add_neg_cancel_right] using he.homotopyHomInv.comp hΦ)

private theorem isHomogeneous_obstructionResidual {ι σM σN σW : Type*} [AddGroup ι]
    [SetLike σM M] [SetLike σN N] [SetLike σW W] [AddMemClass σM M] [AddMemClass σN N]
    [NegMemClass σN N] {𝒜 : ι → σM} {ℬ : ι → σN} {𝒲 : ι → σW} {q r : ι}
    {e : LinearHomotopyEquiv dM dN} (he : e.IsGraded 𝒜 ℬ q) {Φ : W →ₗ[R] M} {Ψ : W →ₗ[R] N}
    (hΦ : LinearMap.IsHomogeneous Φ 𝒲 𝒜 (r + q)) (hΨ : LinearMap.IsHomogeneous Ψ 𝒲 ℬ r) :
    LinearMap.IsHomogeneous (e.obstructionResidual Φ Ψ) 𝒲 ℬ r := by
  rw [obstructionResidual]
  exact hΨ.sub
    (by simpa only [add_zero] using he.hom.comp (isHomogeneous_obstructionInitialLift he hΦ hΨ))

/-- Homogeneity of `obstructionLift` when `e` is graded, `Φ` has degree `r + q`, and `Ψ` has
degree `r`. -/
theorem isHomogeneous_obstructionLift {ι σM σN σW : Type*} [AddGroup ι] [SetLike σM M]
    [SetLike σN N] [SetLike σW W] [AddMemClass σM M] [AddMemClass σN N] [NegMemClass σN N]
    {𝒜 : ι → σM} {ℬ : ι → σN} {𝒲 : ι → σW} {q r : ι} {e : LinearHomotopyEquiv dM dN}
    (he : e.IsGraded 𝒜 ℬ q) {Φ : W →ₗ[R] M} {Ψ : W →ₗ[R] N}
    (hΦ : LinearMap.IsHomogeneous Φ 𝒲 𝒜 (r + q)) (hΨ : LinearMap.IsHomogeneous Ψ 𝒲 ℬ r) :
    LinearMap.IsHomogeneous (e.obstructionLift Φ Ψ) 𝒲 𝒜 r := by
  rw [obstructionLift]
  exact (isHomogeneous_obstructionInitialLift he hΦ hΨ).add
    (by simpa only [add_zero] using he.inv.comp (isHomogeneous_obstructionResidual he hΦ hΨ))

/-- Homogeneity of `obstructionHomotopy` when `e` is graded, `Φ` has degree `r + q`, and `Ψ` has
degree `r`. -/
theorem isHomogeneous_obstructionHomotopy {ι σM σN σW : Type*} [AddGroup ι] [SetLike σM M]
    [SetLike σN N] [SetLike σW W] [AddMemClass σM M] [AddMemClass σN N] [NegMemClass σN N]
    {𝒜 : ι → σM} {ℬ : ι → σN} {𝒲 : ι → σW} {q r : ι} {e : LinearHomotopyEquiv dM dN}
    (he : e.IsGraded 𝒜 ℬ q) {Φ : W →ₗ[R] M} {Ψ : W →ₗ[R] N}
    (hΦ : LinearMap.IsHomogeneous Φ 𝒲 𝒜 (r + q)) (hΨ : LinearMap.IsHomogeneous Ψ 𝒲 ℬ r) :
    LinearMap.IsHomogeneous (e.obstructionHomotopy Φ Ψ) 𝒲 ℬ (r - q) := by
  rw [obstructionHomotopy]
  simpa only [sub_eq_add_neg] using
    he.homotopyInvHom.comp (isHomogeneous_obstructionResidual he hΦ hΨ)

end LinearHomotopyEquiv

end ObstructionDefs

section Obstruction

variable {R : Type uR} {M : Type uM} {N : Type uN} {W : Type uW} [CommSemiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommMonoid W] [Module R W]
  {dM : Module.End R M} {dN : Module.End R N}

namespace LinearHomotopyEquiv

/-- The initial lift already solves `dM ∘ γ₀ - ε • (γ₀ ∘ b) = Φ`. -/
private theorem dM_comp_obstructionInitialLift_sub (e : LinearHomotopyEquiv dM dN)
    {b : Module.End R W} {ε : R} {Φ : W →ₗ[R] M} {Ψ : W →ₗ[R] N}
    (hΦ : dM ∘ₗ Φ + ε • (Φ ∘ₗ b) = 0) (hΨ : dN ∘ₗ Ψ - ε • (Ψ ∘ₗ b) = e.hom ∘ₗ Φ) :
    dM ∘ₗ e.obstructionInitialLift Φ Ψ - ε • (e.obstructionInitialLift Φ Ψ ∘ₗ b) = Φ := by
  have hΦb : ε • (e.homotopyHomInv ∘ₗ Φ ∘ₗ b) = -(e.homotopyHomInv ∘ₗ dM ∘ₗ Φ) := by
    rw [← LinearMap.comp_smul, eq_neg_of_add_eq_zero_right hΦ, LinearMap.comp_neg]
  have hΨb : dM ∘ₗ e.inv ∘ₗ Ψ - ε • (e.inv ∘ₗ Ψ ∘ₗ b) = e.inv ∘ₗ e.hom ∘ₗ Φ := by
    rw [← LinearMap.comp_assoc, e.dM_comp_inv, LinearMap.comp_assoc, ← LinearMap.comp_smul,
      ← LinearMap.comp_sub, hΨ]
  calc
    dM ∘ₗ e.obstructionInitialLift Φ Ψ - ε • (e.obstructionInitialLift Φ Ψ ∘ₗ b)
      = (dM ∘ₗ e.inv ∘ₗ Ψ - ε • (e.inv ∘ₗ Ψ ∘ₗ b)) +
          (dM ∘ₗ e.homotopyHomInv ∘ₗ Φ - ε • (e.homotopyHomInv ∘ₗ Φ ∘ₗ b)) := by
        simp only [obstructionInitialLift, LinearMap.comp_add, LinearMap.add_comp,
          LinearMap.comp_assoc, smul_add]
        abel
    _ = e.inv ∘ₗ e.hom ∘ₗ Φ + (dM ∘ₗ e.homotopyHomInv + e.homotopyHomInv ∘ₗ dM) ∘ₗ Φ := by
        rw [hΨb, hΦb, sub_neg_eq_add, LinearMap.add_comp, LinearMap.comp_assoc,
          LinearMap.comp_assoc]
    _ = Φ := by
        rw [e.dM_comp_homotopyHomInv_add, LinearMap.sub_comp, LinearMap.id_comp,
          LinearMap.comp_assoc, add_sub_cancel]

/-- The residual discrepancy `Ξ` is closed in the sense `dN ∘ Ξ = ε • (Ξ ∘ b)`. -/
private theorem dN_comp_obstructionResidual (e : LinearHomotopyEquiv dM dN)
    {b : Module.End R W} {ε : R} {Φ : W →ₗ[R] M} {Ψ : W →ₗ[R] N}
    (hΦ : dM ∘ₗ Φ + ε • (Φ ∘ₗ b) = 0) (hΨ : dN ∘ₗ Ψ - ε • (Ψ ∘ₗ b) = e.hom ∘ₗ Φ) :
    dN ∘ₗ e.obstructionResidual Φ Ψ = ε • (e.obstructionResidual Φ Ψ ∘ₗ b) := by
  apply sub_eq_zero.1
  calc
    dN ∘ₗ e.obstructionResidual Φ Ψ - ε • (e.obstructionResidual Φ Ψ ∘ₗ b)
      = (dN ∘ₗ Ψ - ε • (Ψ ∘ₗ b)) -
          e.hom ∘ₗ (dM ∘ₗ e.obstructionInitialLift Φ Ψ -
            ε • (e.obstructionInitialLift Φ Ψ ∘ₗ b)) := by
        simp only [obstructionResidual, LinearMap.comp_sub, LinearMap.sub_comp, smul_sub,
          LinearMap.comp_smul, ← LinearMap.comp_assoc, e.dN_comp_hom]
        abel
    _ = 0 := by rw [hΨ, e.dM_comp_obstructionInitialLift_sub hΦ hΨ, sub_self]

/-- **First coupled obstruction equation**: `obstructionLift` bounds the source cocycle `Φ`. -/
theorem dM_comp_obstructionLift_sub (e : LinearHomotopyEquiv dM dN)
    {b : Module.End R W} {ε : R} {Φ : W →ₗ[R] M} {Ψ : W →ₗ[R] N}
    (hΦ : dM ∘ₗ Φ + ε • (Φ ∘ₗ b) = 0) (hΨ : dN ∘ₗ Ψ - ε • (Ψ ∘ₗ b) = e.hom ∘ₗ Φ) :
    dM ∘ₗ e.obstructionLift Φ Ψ - ε • (e.obstructionLift Φ Ψ ∘ₗ b) = Φ := by
  have hΞ : dM ∘ₗ (e.inv ∘ₗ e.obstructionResidual Φ Ψ) -
      ε • ((e.inv ∘ₗ e.obstructionResidual Φ Ψ) ∘ₗ b) = 0 := by
    rw [← LinearMap.comp_assoc, e.dM_comp_inv, LinearMap.comp_assoc,
      e.dN_comp_obstructionResidual hΦ hΨ, LinearMap.comp_smul, LinearMap.comp_assoc, sub_self]
  calc
    dM ∘ₗ e.obstructionLift Φ Ψ - ε • (e.obstructionLift Φ Ψ ∘ₗ b)
      = (dM ∘ₗ e.obstructionInitialLift Φ Ψ - ε • (e.obstructionInitialLift Φ Ψ ∘ₗ b)) +
          (dM ∘ₗ (e.inv ∘ₗ e.obstructionResidual Φ Ψ) -
            ε • ((e.inv ∘ₗ e.obstructionResidual Φ Ψ) ∘ₗ b)) := by
        simp only [obstructionLift, LinearMap.comp_add, LinearMap.add_comp, smul_add]
        abel
    _ = Φ := by rw [e.dM_comp_obstructionInitialLift_sub hΦ hΨ, hΞ, add_zero]

/-- **Second coupled obstruction equation**: `hom ∘ obstructionLift` matches `Ψ` up to the
differential of `obstructionHomotopy`. -/
theorem hom_comp_obstructionLift_add (e : LinearHomotopyEquiv dM dN)
    {b : Module.End R W} {ε : R} {Φ : W →ₗ[R] M} {Ψ : W →ₗ[R] N}
    (hΦ : dM ∘ₗ Φ + ε • (Φ ∘ₗ b) = 0) (hΨ : dN ∘ₗ Ψ - ε • (Ψ ∘ₗ b) = e.hom ∘ₗ Φ) :
    e.hom ∘ₗ e.obstructionLift Φ Ψ +
      (dN ∘ₗ e.obstructionHomotopy Φ Ψ + ε • (e.obstructionHomotopy Φ Ψ ∘ₗ b)) = Ψ := by
  have hη : dN ∘ₗ e.obstructionHomotopy Φ Ψ + ε • (e.obstructionHomotopy Φ Ψ ∘ₗ b) =
      e.obstructionResidual Φ Ψ - e.hom ∘ₗ e.inv ∘ₗ e.obstructionResidual Φ Ψ := by
    rw [obstructionHomotopy]
    calc
      dN ∘ₗ (e.homotopyInvHom ∘ₗ e.obstructionResidual Φ Ψ) +
          ε • ((e.homotopyInvHom ∘ₗ e.obstructionResidual Φ Ψ) ∘ₗ b)
        = dN ∘ₗ e.homotopyInvHom ∘ₗ e.obstructionResidual Φ Ψ +
            e.homotopyInvHom ∘ₗ (ε • (e.obstructionResidual Φ Ψ ∘ₗ b)) := by
          rw [LinearMap.comp_assoc, ← LinearMap.comp_smul]
      _ = (dN ∘ₗ e.homotopyInvHom + e.homotopyInvHom ∘ₗ dN) ∘ₗ e.obstructionResidual Φ Ψ := by
          rw [← e.dN_comp_obstructionResidual hΦ hΨ, LinearMap.add_comp, LinearMap.comp_assoc,
            LinearMap.comp_assoc]
      _ = e.obstructionResidual Φ Ψ - e.hom ∘ₗ e.inv ∘ₗ e.obstructionResidual Φ Ψ := by
          rw [e.dN_comp_homotopyInvHom_add, LinearMap.sub_comp, LinearMap.id_comp,
            LinearMap.comp_assoc]
  rw [hη]
  simp only [obstructionLift, obstructionResidual, LinearMap.comp_add]
  abel

end LinearHomotopyEquiv

end Obstruction

/-! ### Graded homotopy equivalences from quasi-isomorphisms over a division ring -/

namespace InternalGrading

universe uK

variable {K : Type uK} {M : Type uM} {N : Type uN} [DivisionRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (G : InternalGrading K M ℤ) (H : InternalGrading K N ℤ)
  {dM : Module.End K M} {dN : Module.End K N}
  (hdM_hom : LinearMap.IsHomogeneous dM G.piece G.piece 1) (hdM : dM ∘ₗ dM = 0)
  (hdN_hom : LinearMap.IsHomogeneous dN H.piece H.piece 1) (hdN : dN ∘ₗ dN = 0)

/-- A homogeneous chain map of degree zero induces a degree-zero map on graded homology. -/
private theorem isHomogeneous_homologyMap {f : M →ₗ[K] N}
    (hf_hom : LinearMap.IsHomogeneous f G.piece H.piece 0) (hf : f ∘ₗ dM = dN ∘ₗ f) :
    LinearMap.IsHomogeneous (dM.homologyMap f hdM hdN hf) (G.homology hdM_hom hdM).piece
      (H.homology hdN_hom hdN).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p c hc
  rw [add_zero]
  obtain ⟨z, hz, rfl⟩ := (G.mem_homology_piece_iff hdM_hom hdM).1 hc
  rw [LinearMap.homologyπ_apply, LinearMap.homologyMap_mk, ← LinearMap.homologyπ_apply]
  refine H.homologyπ_mem_homology_piece hdN_hom hdN ?_
  simpa only [add_zero] using hf_hom.map_mem hz

/-- Compressing `f` between the homology contractions of `G` and `H` recovers `homologyMap f`. -/
private theorem homologyContraction_proj_comp_comp_incl {f : M →ₗ[K] N}
    (hf : f ∘ₗ dM = dN ∘ₗ f) :
    (H.homologyContraction hdN_hom hdN).proj ∘ₗ f ∘ₗ (G.homologyContraction hdM_hom hdM).incl =
      dM.homologyMap f hdM hdN hf := by
  refine LinearMap.ext fun y ↦ ?_
  have hz := G.homologyContraction_incl_mem_ker hdM_hom hdM y
  have hfz : f ((G.homologyContraction hdM_hom hdM).incl y) ∈ _root_.LinearMap.ker dN :=
    _root_.LinearMap.map_mem_ker_of_comp_eq f hf hz
  have hy := (G.homologyπ_homologyContraction_incl hdM_hom hdM y).symm
  conv_rhs => rw [hy, LinearMap.homologyπ_apply, LinearMap.homologyMap_mk]
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    H.homologyContraction_proj_of_mem_ker hdN_hom hdN hfz, LinearMap.homologyπ_apply]

/-- Left homotopy identity `dM ∘ (hM - g ∘ f ∘ hM) + (hM - g ∘ f ∘ hM) ∘ dM = 1 - g ∘ f` when
`dM ∘ g = 0 = g ∘ dN` and `g ∘ f ∘ iM = iM`. -/
private theorem homologyInverse_homotopyHomInv_eq {P : Type*} [AddCommGroup P] [Module K P]
    (cM : LinearContraction dM (0 : Module.End K P)) {f : M →ₗ[K] N} {g : N →ₗ[K] M}
    (hf : f ∘ₗ dM = dN ∘ₗ f) (hdg : dM ∘ₗ g = 0) (hgd : g ∘ₗ dN = 0)
    (hgfi : g ∘ₗ f ∘ₗ cM.incl = cM.incl) :
    dM ∘ₗ (cM.homotopy - g ∘ₗ f ∘ₗ cM.homotopy) +
      (cM.homotopy - g ∘ₗ f ∘ₗ cM.homotopy) ∘ₗ dM = LinearMap.id - g ∘ₗ f := by
  have h1 : dM ∘ₗ (g ∘ₗ f ∘ₗ cM.homotopy) = 0 := by
    rw [← LinearMap.comp_assoc, hdg, LinearMap.zero_comp]
  have h2 : (g ∘ₗ f ∘ₗ cM.homotopy) ∘ₗ dM = g ∘ₗ f - cM.incl ∘ₗ cM.proj := by
    calc
      (g ∘ₗ f ∘ₗ cM.homotopy) ∘ₗ dM
        = g ∘ₗ f ∘ₗ (LinearMap.id - cM.incl ∘ₗ cM.proj - dM ∘ₗ cM.homotopy) := by
          rw [LinearMap.comp_assoc, LinearMap.comp_assoc,
            eq_sub_of_add_eq' cM.dM_comp_homotopy_add_homotopy_comp_dM, sub_right_comm]
      _ = g ∘ₗ f - (g ∘ₗ f ∘ₗ cM.incl) ∘ₗ cM.proj - (g ∘ₗ dN) ∘ₗ f ∘ₗ cM.homotopy := by
          simp only [LinearMap.comp_sub, LinearMap.comp_id, ← LinearMap.comp_assoc, hf]
      _ = g ∘ₗ f - cM.incl ∘ₗ cM.proj := by rw [hgfi, hgd, LinearMap.zero_comp, sub_zero]
  calc
    dM ∘ₗ (cM.homotopy - g ∘ₗ f ∘ₗ cM.homotopy) + (cM.homotopy - g ∘ₗ f ∘ₗ cM.homotopy) ∘ₗ dM
      = (dM ∘ₗ cM.homotopy + cM.homotopy ∘ₗ dM) -
          (dM ∘ₗ (g ∘ₗ f ∘ₗ cM.homotopy) + (g ∘ₗ f ∘ₗ cM.homotopy) ∘ₗ dM) := by
        rw [LinearMap.comp_sub, LinearMap.sub_comp]
        abel
    _ = LinearMap.id - g ∘ₗ f := by
        rw [cM.dM_comp_homotopy_add_homotopy_comp_dM, h1, zero_add, h2]
        abel

/-- Right homotopy identity `dN ∘ (hN - hN ∘ f ∘ g) + (hN - hN ∘ f ∘ g) ∘ dN = 1 - f ∘ g` when
`dM ∘ g = 0 = g ∘ dN` and `pN ∘ f ∘ g = pN`. -/
private theorem homologyInverse_homotopyInvHom_eq {Q : Type*} [AddCommGroup Q] [Module K Q]
    (cN : LinearContraction dN (0 : Module.End K Q)) {f : M →ₗ[K] N} {g : N →ₗ[K] M}
    (hf : f ∘ₗ dM = dN ∘ₗ f) (hdg : dM ∘ₗ g = 0) (hgd : g ∘ₗ dN = 0)
    (hpfg : cN.proj ∘ₗ f ∘ₗ g = cN.proj) :
    dN ∘ₗ (cN.homotopy - cN.homotopy ∘ₗ f ∘ₗ g) +
      (cN.homotopy - cN.homotopy ∘ₗ f ∘ₗ g) ∘ₗ dN = LinearMap.id - f ∘ₗ g := by
  have h1 : (cN.homotopy ∘ₗ f ∘ₗ g) ∘ₗ dN = 0 := by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hgd, LinearMap.comp_zero, LinearMap.comp_zero]
  have hdnf : dN ∘ₗ (f ∘ₗ g) = f ∘ₗ (dM ∘ₗ g) := by
    rw [← LinearMap.comp_assoc, ← hf, LinearMap.comp_assoc]
  have h2 : dN ∘ₗ (cN.homotopy ∘ₗ f ∘ₗ g) = f ∘ₗ g - cN.incl ∘ₗ cN.proj := by
    calc
      dN ∘ₗ (cN.homotopy ∘ₗ f ∘ₗ g)
        = (LinearMap.id - cN.incl ∘ₗ cN.proj - cN.homotopy ∘ₗ dN) ∘ₗ f ∘ₗ g := by
          rw [← LinearMap.comp_assoc,
            eq_sub_of_add_eq cN.dM_comp_homotopy_add_homotopy_comp_dM, sub_right_comm]
      _ = f ∘ₗ g - cN.incl ∘ₗ (cN.proj ∘ₗ f ∘ₗ g) - cN.homotopy ∘ₗ f ∘ₗ (dM ∘ₗ g) := by
          simp only [LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc, hdnf]
      _ = f ∘ₗ g - cN.incl ∘ₗ cN.proj := by
          rw [hpfg, hdg, LinearMap.comp_zero, LinearMap.comp_zero, sub_zero]
  calc
    dN ∘ₗ (cN.homotopy - cN.homotopy ∘ₗ f ∘ₗ g) + (cN.homotopy - cN.homotopy ∘ₗ f ∘ₗ g) ∘ₗ dN
      = (dN ∘ₗ cN.homotopy + cN.homotopy ∘ₗ dN) -
          (dN ∘ₗ (cN.homotopy ∘ₗ f ∘ₗ g) + (cN.homotopy ∘ₗ f ∘ₗ g) ∘ₗ dN) := by
        rw [LinearMap.comp_sub, LinearMap.sub_comp]
        abel
    _ = LinearMap.id - f ∘ₗ g := by
        rw [cN.dM_comp_homotopy_add_homotopy_comp_dM, h1, add_zero, h2]
        abel

/-- Over a division ring, any degree-zero chain map between internally `ℤ`-graded modules with
square-zero degree-one differentials that induces a bijection on homology extends to a
`LinearHomotopyEquiv` with that exact forward map. -/
noncomputable def linearHomotopyEquivOfBijectiveHomologyMap {f : M →ₗ[K] N}
    (hf : f ∘ₗ dM = dN ∘ₗ f) (hbij : Function.Bijective (dM.homologyMap f hdM hdN hf)) :
    LinearHomotopyEquiv dM dN :=
  let cM := G.homologyContraction hdM_hom hdM
  let cN := H.homologyContraction hdN_hom hdN
  let φ := LinearEquiv.ofBijective (dM.homologyMap f hdM hdN hf) hbij
  let g : N →ₗ[K] M := cM.incl ∘ₗ φ.symm.toLinearMap ∘ₗ cN.proj
  have hpfi : cN.proj ∘ₗ f ∘ₗ cM.incl = φ.toLinearMap :=
    G.homologyContraction_proj_comp_comp_incl H hdM_hom hdM hdN_hom hdN hf
  have hdg : dM ∘ₗ g = 0 := by simp [g]
  have hgd : g ∘ₗ dN = 0 := by
    simp only [g, LinearMap.comp_assoc, cN.proj_comp_dM, LinearMap.zero_comp, LinearMap.comp_zero]
  have hgfi : g ∘ₗ f ∘ₗ cM.incl = cM.incl := by
    calc
      g ∘ₗ f ∘ₗ cM.incl = cM.incl ∘ₗ φ.symm.toLinearMap ∘ₗ (cN.proj ∘ₗ f ∘ₗ cM.incl) := by
        simp only [g, LinearMap.comp_assoc]
      _ = cM.incl := by rw [hpfi, LinearEquiv.symm_comp, LinearMap.comp_id]
  have hφp : φ.toLinearMap ∘ₗ (φ.symm.toLinearMap ∘ₗ cN.proj) = cN.proj := by
    rw [← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]
  have hpfg : cN.proj ∘ₗ f ∘ₗ g = cN.proj := by
    calc
      cN.proj ∘ₗ f ∘ₗ g = (cN.proj ∘ₗ f ∘ₗ cM.incl) ∘ₗ (φ.symm.toLinearMap ∘ₗ cN.proj) := by
        simp only [g, LinearMap.comp_assoc]
      _ = cN.proj := by rw [hpfi, hφp]
  { hom := f
    inv := g
    homotopyHomInv := cM.homotopy - g ∘ₗ f ∘ₗ cM.homotopy
    homotopyInvHom := cN.homotopy - cN.homotopy ∘ₗ f ∘ₗ g
    dN_comp_hom := hf.symm
    dM_comp_inv := hdg.trans hgd.symm
    dM_comp_homotopyHomInv_add :=
      homologyInverse_homotopyHomInv_eq cM.toLinearContraction hf hdg hgd hgfi
    dN_comp_homotopyInvHom_add :=
      homologyInverse_homotopyInvHom_eq cN.toLinearContraction hf hdg hgd hpfg }

/-- The forward map of `linearHomotopyEquivOfBijectiveHomologyMap` is `f`. -/
@[simp]
theorem linearHomotopyEquivOfBijectiveHomologyMap_hom {f : M →ₗ[K] N}
    (hf : f ∘ₗ dM = dN ∘ₗ f) (hbij : Function.Bijective (dM.homologyMap f hdM hdN hf)) :
    (G.linearHomotopyEquivOfBijectiveHomologyMap H hdM_hom hdM hdN_hom hdN hf hbij).hom = f :=
  (rfl)

/-- The homotopy equivalence constructed from a degree-zero quasi-isomorphism over a division ring
is compatible with the gradings: its inverse has degree zero and its homotopies have degree `-1`. -/
theorem isGraded_linearHomotopyEquivOfBijectiveHomologyMap {f : M →ₗ[K] N}
    (hf_hom : LinearMap.IsHomogeneous f G.piece H.piece 0) (hf : f ∘ₗ dM = dN ∘ₗ f)
    (hbij : Function.Bijective (dM.homologyMap f hdM hdN hf)) :
    (G.linearHomotopyEquivOfBijectiveHomologyMap H hdM_hom hdM hdN_hom hdN hf hbij).IsGraded
      G.piece H.piece 1 := by
  set e := G.linearHomotopyEquivOfBijectiveHomologyMap H hdM_hom hdM hdN_hom hdN hf hbij
  let φ := LinearEquiv.ofBijective (dM.homologyMap f hdM hdN hf) hbij
  have hφ_symm : LinearMap.IsHomogeneous φ.symm.toLinearMap
      (H.homology hdN_hom hdN).piece (G.homology hdM_hom hdM).piece 0 :=
    (G.isHomogeneous_homologyMap H hdM_hom hdM hdN_hom hdN hf_hom hf).linearEquiv_symm
  have hg_def : e.inv = (G.homologyContraction hdM_hom hdM).incl ∘ₗ φ.symm.toLinearMap ∘ₗ
      (H.homologyContraction hdN_hom hdN).proj := rfl
  have hg : LinearMap.IsHomogeneous e.inv H.piece G.piece 0 := by
    rw [hg_def]
    simpa only [zero_add] using
      (G.isHomogeneous_homologyContraction_incl hdM_hom hdM).comp
        (hφ_symm.comp (H.isHomogeneous_homologyContraction_proj hdN_hom hdN))
  have hhM : e.homotopyHomInv =
      (G.homologyContraction hdM_hom hdM).homotopy -
        e.inv ∘ₗ f ∘ₗ (G.homologyContraction hdM_hom hdM).homotopy := rfl
  have hhN : e.homotopyInvHom =
      (H.homologyContraction hdN_hom hdN).homotopy -
        (H.homologyContraction hdN_hom hdN).homotopy ∘ₗ f ∘ₗ e.inv := rfl
  have hcM := G.isHomogeneous_homologyContraction_homotopy hdM_hom hdM
  have hcN := H.isHomogeneous_homologyContraction_homotopy hdN_hom hdN
  refine ⟨hf_hom, hg, ?_, ?_⟩
  · rw [hhM]
    exact hcM.sub (by simpa only [zero_add, add_zero] using hg.comp (hf_hom.comp hcM))
  · rw [hhN]
    exact hcN.sub (by simpa only [zero_add, add_zero] using hcN.comp (hf_hom.comp hg))

end InternalGrading

end TauCeti
