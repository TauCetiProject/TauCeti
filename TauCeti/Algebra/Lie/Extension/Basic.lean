/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.Extension
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Extensions built from 2-cocycles

A 2-cocycle `c` of a Lie algebra `L` with values in an `L`-module `M` shears the bracket of `L × M`.
Mathlib's `LieAlgebra.ofTwoCocycle c` is this Lie algebra, and Mathlib packages it as an extension
(`LieAlgebra.Extension.ofTwoCocycle`) only when `M` is itself given the structure of an abelian Lie
algebra.

This file supplies cocycle-model constructions for arbitrary coefficient modules `M`,
and comparisons with extensions whose kernels are themselves abelian Lie algebras:

* `LieAlgebra.ofProdLinearEquiv`: the identification `LieAlgebra.ofProd` with `L × M` as a linear
  equivalence, so that finiteness transfers to `LieAlgebra.ofTwoCocycle c`;
* `LieAlgebra.ofTwoCocycle.proj`: the projection onto `L` as a surjective Lie algebra
  homomorphism, whose kernel `0 × M` is an abelian ideal;
* `LieAlgebra.ofTwoCocycle.map` and `LieAlgebra.ofTwoCocycle.mapEquiv`: for trivial coefficients,
  the morphisms and isomorphisms of central extensions `(x, m) ↦ (φ x, e m)` induced by a map `φ`
  of the quotients and a linear map `e` of the kernels carrying one cocycle to the other;
* `LieAlgebra.ofTwoCocycle.sectionOfVanishing` and
  `LieAlgebra.ofTwoCocycle.splitEquivOfVanishing`: the zero-coefficient Lie section over a
  subalgebra where the cocycle vanishes, and, for trivial coefficients, the direct-product
  splitting of its preimage;
* `LieAlgebra.ofTwoCocycle.derivation`: for trivial coefficients, the derivation
  `(x, m) ↦ (D x, 0)` induced by a derivation `D` of the quotient for which the cocycle is skew;
* `LieAlgebra.ofTwoCocycle.centralElement`: for coefficients the trivial module `R`, the central
  element `K = (0, 1)`, which is nonzero over a nontrivial ring, and in terms of which every
  element is an element of `L` plus a multiple of `K`
  (`LieAlgebra.ofTwoCocycle.ofProd_eq_add_smul_centralElement`);
* `LieAlgebra.Extension.ofTwoCocycleEquiv`: the comparison of an extension with abelian kernel
  and a linear section with the model of Mathlib's native `Extension.twoCocycleOf`.

The construction of `map` and `mapEquiv` follows Mathlib's `LieAlgebra.LieEquiv.ofCoboundary`,
which identifies the extensions of cohomologous cocycles by acting on the coordinates of `ofProd`.
Here the coordinates are instead transformed by a map of quotients and a map of kernels.

These let structure theorems about abelian ideals, such as the existence of Levi complements, be
applied to the sheared Lie algebra, for instance to show that a 2-cocycle is a coboundary. The
morphisms of central extensions compare the extensions attached to proportional cocycles, and an
extension with its restriction to a subalgebra. The degree-one counterpart, the module sheared by
a Lie derivation, is `LieDerivation.ShearedModule` in `TauCeti.Algebra.Lie.Derivation.Cocycle`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for cocycle models of extensions.
-/

public section

open LieModule.Cohomology

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

namespace LieAlgebra

variable (c : twoCocycle R L M)

/-- The identification `LieAlgebra.ofProd` of `L × M` with the Lie algebra sheared by a 2-cocycle,
as a linear equivalence. -/
def ofProdLinearEquiv : (L × M) ≃ₗ[R] ofTwoCocycle c where
  __ := ofProd c
  map_add' := of_add c
  map_smul' := of_smul c

@[simp]
lemma coe_ofProdLinearEquiv : ⇑(ofProdLinearEquiv c) = ofProd c := (rfl)

@[simp]
lemma coe_ofProdLinearEquiv_symm : ⇑(ofProdLinearEquiv c).symm = (ofProd c).symm := (rfl)

instance [Module.Finite R L] [Module.Finite R M] : Module.Finite R (ofTwoCocycle c) :=
  Module.Finite.equiv (ofProdLinearEquiv c)

namespace ofTwoCocycle

/-- The projection of the Lie algebra sheared by a 2-cocycle onto `L`, as a Lie algebra
homomorphism. -/
def proj : ofTwoCocycle c →ₗ⁅R⁆ L where
  toFun x := ((ofProd c).symm x).1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' {_ _} := by simp [bracket_ofTwoCocycle]

@[simp]
lemma proj_apply (x : ofTwoCocycle c) : proj c x = ((ofProd c).symm x).1 := (rfl)

lemma proj_surjective : Function.Surjective (proj c) :=
  fun x ↦ ⟨ofProd c (x, 0), by simp⟩

lemma mem_ker_proj {x : ofTwoCocycle c} : x ∈ (proj c).ker ↔ ((ofProd c).symm x).1 = 0 :=
  LieHom.mem_ker

/-- The kernel `0 × M` of the projection is an abelian ideal. -/
instance : IsLieAbelian (proj c).ker where
  trivial a b := by
    have ha := (mem_ker_proj c).1 a.2
    have hb := (mem_ker_proj c).1 b.2
    refine Subtype.ext ((ofProd c).symm.injective ?_)
    simp [bracket_ofTwoCocycle, ha, hb]

/-- The zero-coefficient Lie section over a subalgebra on which the cocycle vanishes.
No triviality assumption on the coefficient action is needed. -/
def sectionOfVanishing (S : LieSubalgebra R L)
    (hc : ∀ x ∈ S, ∀ y ∈ S, (c : twoCochain R L M) x y = 0) :
    S →ₗ⁅R⁆ ofTwoCocycle c where
  toFun x := ofProd c (x, 0)
  map_add' _ _ := by simp [← of_add]
  map_smul' _ _ := by simp [← of_smul]
  map_lie' {x y} := by simp [bracket_ofTwoCocycle, hc x x.property y y.property]

/-- The section has zero coefficient coordinate. -/
@[simp]
lemma sectionOfVanishing_apply (S : LieSubalgebra R L)
    (hc : ∀ x ∈ S, ∀ y ∈ S, (c : twoCochain R L M) x y = 0) (x : S) :
    sectionOfVanishing c S hc x = ofProd c (x, 0) := (rfl)

/-- A central extension splits over a subalgebra where its cocycle vanishes. The coefficient
coordinate is expressed in any chosen abelian Lie algebra `N` linearly equivalent to `M`. -/
def splitEquivOfVanishing [LieModule.IsTrivial L M]
    {N : Type*} [LieRing N] [LieAlgebra R N] [IsLieAbelian N]
    (S : LieSubalgebra R L) (e : M ≃ₗ[R] N)
    (hc : ∀ x ∈ S, ∀ y ∈ S, (c : twoCochain R L M) x y = 0) :
    (S × N) ≃ₗ⁅R⁆ S.comap (proj c) where
  toFun p := ⟨ofProd c (p.1, e.symm p.2), by simp⟩
  invFun v := (⟨proj c v, v.property⟩, e ((ofProd c).symm v).2)
  left_inv p := by simp
  right_inv v := Subtype.ext (by simp [proj_apply])
  map_add' p q := Subtype.ext (by simp [← of_add])
  map_smul' r p := Subtype.ext (by simp [← of_smul])
  map_lie' {p q} := by
    apply Subtype.ext
    simp [bracket_ofTwoCocycle, trivial_lie_zero, hc p.1 p.1.property q.1 q.1.property,
      LieAlgebra.Prod.bracket_apply]

/-- Forward coordinates of the split preimage. -/
@[simp]
lemma coe_splitEquivOfVanishing [LieModule.IsTrivial L M]
    {N : Type*} [LieRing N] [LieAlgebra R N] [IsLieAbelian N]
    (S : LieSubalgebra R L) (e : M ≃ₗ[R] N)
    (hc : ∀ x ∈ S, ∀ y ∈ S, (c : twoCochain R L M) x y = 0) (p : S × N) :
    (splitEquivOfVanishing c S e hc p : ofTwoCocycle c) = ofProd c (p.1, e.symm p.2) :=
  (rfl)

/-- Inverse coordinates of the split preimage. -/
@[simp]
lemma splitEquivOfVanishing_symm_apply [LieModule.IsTrivial L M]
    {N : Type*} [LieRing N] [LieAlgebra R N] [IsLieAbelian N]
    (S : LieSubalgebra R L) (e : M ≃ₗ[R] N)
    (hc : ∀ x ∈ S, ∀ y ∈ S, (c : twoCochain R L M) x y = 0)
    (v : S.comap (proj c)) :
    (splitEquivOfVanishing c S e hc).symm v =
      (⟨proj c v, v.property⟩, e ((ofProd c).symm v).2) := (rfl)

section Trivial

/-! ### Morphisms of central extensions -/

variable {L' M' : Type*} [LieRing L'] [LieAlgebra R L'] [AddCommGroup M'] [Module R M']
  [LieRingModule L' M'] [LieModule R L' M'] [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M']

/-- The morphism of central extensions `(x, m) ↦ (φ x, e m)` from the Lie algebra sheared by a
2-cocycle `c` with trivial coefficients to the one sheared by `c'`, for a Lie algebra morphism `φ`
and a linear map `e` of coefficients such that `c' (φ x) (φ y) = e (c x y)`.

With `φ` the identity this pushes an extension forward along a map of its kernels; with `e` the
identity it compares an extension with the pullback of another along `φ`. -/
def map (φ : L →ₗ⁅R⁆ L') (e : M →ₗ[R] M') (c' : twoCocycle R L' M')
    (h : ∀ x y, (c' : twoCochain R L' M') (φ x) (φ y) = e ((c : twoCochain R L M) x y)) :
    ofTwoCocycle c →ₗ⁅R⁆ ofTwoCocycle c' where
  toFun v := ofProd c' (φ ((ofProd c).symm v).1, e ((ofProd c).symm v).2)
  map_add' _ _ := by simp [← of_add]
  map_smul' _ _ := by simp [← of_smul]
  map_lie' {_ _} := by simp [bracket_ofTwoCocycle, trivial_lie_zero, h]

section Map

variable (φ : L →ₗ⁅R⁆ L') (e : M →ₗ[R] M') (c' : twoCocycle R L' M')
  (h : ∀ x y, (c' : twoCochain R L' M') (φ x) (φ y) = e ((c : twoCochain R L M) x y))

/-- A morphism of central extensions acts by `φ` on the first coordinate and `e` on the
second. -/
@[simp]
lemma map_ofProd (x : L) (m : M) : map c φ e c' h (ofProd c (x, m)) = ofProd c' (φ x, e m) :=
  (rfl)

@[simp]
lemma ofProd_symm_map (v : ofTwoCocycle c) :
    (ofProd c').symm (map c φ e c' h v) = (φ ((ofProd c).symm v).1, e ((ofProd c).symm v).2) :=
  (rfl)

/-- A morphism of central extensions lies over the morphism `φ` of the quotients. -/
lemma proj_map (v : ofTwoCocycle c) : proj c' (map c φ e c' h v) = φ (proj c v) :=
  (rfl)

/-- The identity morphism of a central extension. -/
@[simp]
lemma map_id : map c (LieHom.id : L →ₗ⁅R⁆ L) LinearMap.id c (fun _ _ ↦ rfl) = LieHom.id :=
  LieHom.ext fun _ ↦ rfl

/-- Morphisms of central extensions compose by composing the maps of quotients and kernels. -/
lemma map_comp {L'' M'' : Type*} [LieRing L''] [LieAlgebra R L''] [AddCommGroup M'']
    [Module R M''] [LieRingModule L'' M''] [LieModule R L'' M''] [LieModule.IsTrivial L'' M'']
    (φ' : L' →ₗ⁅R⁆ L'') (e' : M' →ₗ[R] M'') (c'' : twoCocycle R L'' M'')
    (h' : ∀ x y, (c'' : twoCochain R L'' M'') (φ' x) (φ' y) = e' ((c' : twoCochain R L' M') x y)) :
    (map c' φ' e' c'' h').comp (map c φ e c' h) =
      map c (φ'.comp φ) (e' ∘ₗ e) c'' (fun x y ↦ by simp [h', h]) :=
  LieHom.ext fun _ ↦ rfl

/-- A morphism of central extensions is injective when the maps of quotients and kernels are. -/
lemma map_injective (hφ : Function.Injective φ) (he : Function.Injective e) :
    Function.Injective (map c φ e c' h) :=
  (ofProd c').injective.comp ((hφ.prodMap he).comp (ofProd c).symm.injective)

/-- A morphism of central extensions is surjective when the maps of quotients and kernels are. -/
lemma map_surjective (hφ : Function.Surjective φ) (he : Function.Surjective e) :
    Function.Surjective (map c φ e c' h) :=
  (ofProd c').surjective.comp ((hφ.prodMap he).comp (ofProd c).symm.surjective)

end Map

variable (φ : L ≃ₗ⁅R⁆ L') (e : M ≃ₗ[R] M') (c' : twoCocycle R L' M')
  (h : ∀ x y, (c' : twoCochain R L' M') (φ x) (φ y) = e ((c : twoCochain R L M) x y))

/-- The isomorphism of central extensions `(x, m) ↦ (φ x, e m)` induced by isomorphisms `φ` of
the quotients and `e` of the kernels such that `c' (φ x) (φ y) = e (c x y)`. -/
def mapEquiv : ofTwoCocycle c ≃ₗ⁅R⁆ ofTwoCocycle c' where
  __ := map c φ.toLieHom e.toLinearMap c' h
  invFun := map c' φ.symm.toLieHom e.symm.toLinearMap c fun x y ↦ by
    simpa using congrArg e.symm (h (φ.symm x) (φ.symm y)).symm
  left_inv v := (ofProd c).symm.injective (by simp)
  right_inv v := (ofProd c').symm.injective (by simp)

@[simp]
lemma mapEquiv_ofProd (x : L) (m : M) :
    mapEquiv c φ e c' h (ofProd c (x, m)) = ofProd c' (φ x, e m) :=
  (rfl)

@[simp]
lemma ofProd_symm_mapEquiv (v : ofTwoCocycle c) :
    (ofProd c').symm (mapEquiv c φ e c' h v) = (φ ((ofProd c).symm v).1, e ((ofProd c).symm v).2) :=
  (rfl)

@[simp]
lemma mapEquiv_symm_ofProd (x : L') (m : M') :
    (mapEquiv c φ e c' h).symm (ofProd c' (x, m)) = ofProd c (φ.symm x, e.symm m) :=
  (rfl)

@[simp]
lemma toLieHom_mapEquiv :
    (mapEquiv c φ e c' h).toLieHom = map c φ.toLieHom e.toLinearMap c' h :=
  (rfl)

section Derivation

variable (D : LieDerivation R L L)
  (hD : ∀ x y, (c : twoCochain R L M) (D x) y + (c : twoCochain R L M) x (D y) = 0)
include hD

/-- The derivation `(x, m) ↦ (D x, 0)` of the Lie algebra sheared by a 2-cocycle `c` with trivial
coefficients, for a derivation `D` of `L` which is skew for `c`:
`c (D x) y + c x (D y) = 0`. It kills the central kernel `0 × M`. -/
def derivation : LieDerivation R (ofTwoCocycle c) (ofTwoCocycle c) where
  toFun v := ofProd c (D ((ofProd c).symm v).1, 0)
  map_add' _ _ := by simp [← of_add]
  map_smul' _ _ := by simp [← of_smul]
  leibniz' v w := by
    -- Subtraction on the sheared Lie algebra is transported from `L × M`.
    have hsub (a b : ofTwoCocycle c) :
        (ofProd c).symm (a - b) = (ofProd c).symm a - (ofProd c).symm b := (rfl)
    refine (ofProd c).symm.injective (Prod.ext ?_ ?_)
    · simp [bracket_ofTwoCocycle, hsub, LieDerivation.apply_lie_eq_sub]
    · have h := hD ((ofProd c).symm v).1 ((ofProd c).symm w).1
      rw [← twoCochain_skew _ ((ofProd c).symm w).1] at h
      simp only [LinearMap.coe_mk, AddHom.coe_mk, bracket_ofTwoCocycle, hsub,
        Equiv.symm_apply_apply, trivial_lie_zero, sub_zero, add_zero, Prod.snd_sub,
        twoCochain_val_apply]
      rw [← h]
      abel

/-- The derivation acts by `D` on the first coordinate and kills the second. -/
@[simp]
lemma derivation_ofProd (x : L) (m : M) :
    derivation c D hD (ofProd c (x, m)) = ofProd c (D x, 0) :=
  (rfl)

@[simp]
lemma ofProd_symm_derivation (v : ofTwoCocycle c) :
    (ofProd c).symm (derivation c D hD v) = (D ((ofProd c).symm v).1, 0) :=
  (rfl)

/-- The derivation lies over `D`. -/
lemma proj_derivation (v : ofTwoCocycle c) : proj c (derivation c D hD v) = D (proj c v) :=
  (rfl)

end Derivation

end Trivial

end ofTwoCocycle

namespace Extension

noncomputable section

open Function

variable {M : Type*} [LieRing M] [LieAlgebra R M] (E : Extension R M L)

/-- The kernel equivalence is the inclusion on underlying elements. -/
@[simp]
theorem coe_toKer (m : M) : (E.toKer m : E.L) = E.incl m := (rfl)

/-- Inverting the kernel equivalence recovers the underlying element by inclusion. -/
@[simp]
theorem incl_toKer_symm (v : E.proj.ker) : E.incl (E.toKer.symm v) = v := by
  rw [← coe_toKer, LieEquiv.apply_symm_apply]

variable {s : L →ₗ[R] E.L} (hs : LeftInverse E.proj s)

/-- The kernel coordinate relative to a linear section, namely `x - s (proj x)`. -/
def splittingCoordinate : E.L →ₗ[R] M :=
  E.toKer.symm.toLinearMap.comp
    ((LinearMap.id - s.comp E.proj.toLinearMap).codRestrict E.proj.ker.toSubmodule
      (fun x ↦ by simp [hs.eq]))

/-- Evaluate the kernel coordinate by inverting the kernel equivalence on the difference
from the section. -/
theorem splittingCoordinate_apply (x : E.L) :
    E.splittingCoordinate hs x =
      E.toKer.symm ⟨x - s (E.proj x), by simp [hs.eq]⟩ := by
  -- Evaluation of the composite and its codomain restriction gives this kernel element.
  rfl

/-- Including the kernel coordinate gives the difference from the section. -/
@[simp]
theorem incl_splittingCoordinate (x : E.L) :
    E.incl (E.splittingCoordinate hs x) = x - s (E.proj x) := by
  rw [splittingCoordinate_apply, incl_toKer_symm]

/-- The kernel coordinate vanishes on the section. -/
@[simp]
theorem splittingCoordinate_section (x : L) : E.splittingCoordinate hs (s x) = 0 := by
  apply E.incl_injective
  simp [hs x]

/-- The kernel coordinate is a retraction of the inclusion. -/
@[simp]
theorem splittingCoordinate_incl (m : M) : E.splittingCoordinate hs (E.incl m) = m := by
  apply E.incl_injective
  simp

variable [IsLieAbelian M]

/-- Including the native cocycle gives the defect of the section from preserving brackets. -/
theorem incl_twoCocycleOf (x y : L) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    E.incl ((E.twoCocycleOf hs : L →ₗ[R] L →ₗ[R] M) x y) = ⁅s x, s y⁆ - s ⁅x, y⁆ := by
  -- Mathlib's native cocycle is the kernel-valued bracket defect composed with `toKer.symm`.
  simp only [twoCocycleOf_coe_coe, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
    LieEquiv.coe_toLinearEquiv, incl_toKer_symm]
  -- The underlying value of Mathlib's private `twoCocycleAux` is this bracket defect.
  rfl

/-- The induced quotient action is computed by the bracket with the lift along any linear
section. -/
theorem incl_lie (hs : LeftInverse E.proj s) (x : L) (m : M) :
    letI := E.ringModuleOf
    E.incl ⁅x, m⁆ = ⁅s x, E.incl m⁆ := by
  let := E.ringModuleOf
  have h := E.ringModuleOf_bracket_proj m (s x)
  rw [hs x] at h
  rw [h, incl_toKer_symm, LieSubmodule.coe_bracket, lie_toKer_apply]

/-- A split extension with abelian kernel is isomorphic to the model of its native cocycle.
The coordinates are `s x + incl m`; the section itself need not preserve brackets. -/
def ofTwoCocycleEquiv :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    LieAlgebra.ofTwoCocycle (E.twoCocycleOf hs) ≃ₗ⁅R⁆ E.L := by
  letI := E.ringModuleOf
  letI := E.lieModuleOf
  let c := E.twoCocycleOf hs
  exact
    { toFun v := s ((ofProd c).symm v).1 + E.incl ((ofProd c).symm v).2
      invFun x := ofProd c (E.proj x, E.splittingCoordinate hs x)
      map_add' _ _ := by simp; abel
      map_smul' _ _ := by simp [smul_add]
      left_inv v := by
        apply (ofProd c).symm.injective
        simp [hs.eq]
      right_inv x := by simp
      map_lie' {v w} := by
        simp only [bracket_ofTwoCocycle, c, Equiv.symm_apply_apply, map_sub, map_add]
        rw [E.incl_twoCocycleOf hs, E.incl_lie hs, E.incl_lie hs]
        simp only [lie_add, add_lie, ← LieHom.map_lie, trivial_lie_zero M M, map_zero,
          add_zero]
        rw [← lie_skew (s ((ofProd c).symm w).1) (E.incl ((ofProd c).symm v).2)]
        abel }

/-- The comparison sends product coordinates to the section plus the inclusion. -/
@[simp]
theorem ofTwoCocycleEquiv_ofProd (x : L) (m : M) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    E.ofTwoCocycleEquiv hs (ofProd (E.twoCocycleOf hs) (x, m)) = s x + E.incl m := (rfl)

/-- The inverse comparison consists of the projection and the kernel coordinate. -/
@[simp]
theorem ofTwoCocycleEquiv_symm_apply (x : E.L) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    (E.ofTwoCocycleEquiv hs).symm x =
      ofProd (E.twoCocycleOf hs) (E.proj x, E.splittingCoordinate hs x) := (rfl)

/-- The comparison is over the identity on the quotient. -/
@[simp]
theorem proj_ofTwoCocycleEquiv :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    ∀ v, E.proj (E.ofTwoCocycleEquiv hs v) = ofTwoCocycle.proj (E.twoCocycleOf hs) v := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  intro v
  obtain ⟨⟨x, m⟩, rfl⟩ := (ofProd (E.twoCocycleOf hs)).surjective v
  simp [hs x]

/-- The native cocycle is the kernel coordinate of the bracket of section elements. -/
theorem twoCocycleOf_eq_splittingCoordinate (x y : L) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    (E.twoCocycleOf hs : L →ₗ[R] L →ₗ[R] M) x y =
      E.splittingCoordinate hs ⁅s x, s y⁆ := by
  apply E.incl_injective
  simp [hs.eq, LieHom.map_lie]

end

end Extension

end LieAlgebra

/-! ### The central element of an extension by `R` -/

namespace LieAlgebra.ofTwoCocycle

variable (c : twoCocycle R L (TrivialLieModule R L R))

/-- The central element `K = (0, 1)` of the central extension of a Lie algebra by `R` defined by a
2-cocycle `c` with trivial coefficients, such as the residue cocycle of formal or of polynomial
currents. -/
def centralElement : ofTwoCocycle c :=
  ofProd c (0, (TrivialLieModule.equiv R L R).symm 1)

/-- The coordinates of `K` are `(0, 1)`. -/
@[simp]
theorem ofProd_symm_centralElement :
    (ofProd c).symm (centralElement c) = (0, (TrivialLieModule.equiv R L R).symm 1) := by
  rw [centralElement, Equiv.symm_apply_apply]

/-- The element `K` is central. -/
theorem centralElement_mem_center : centralElement c ∈ center R (ofTwoCocycle c) :=
  (LieModule.mem_maxTrivSubmodule R _ _ _).2 fun v ↦ by
    simp only [centralElement, bracket_ofTwoCocycle, Equiv.symm_apply_apply, lie_zero,
      trivial_lie_zero, map_zero, sub_zero, add_zero]
    exact of_zero c

/-- The element `K` is nonzero over a nontrivial ring. -/
theorem centralElement_ne_zero [Nontrivial R] : centralElement c ≠ 0 := by
  intro h
  have h' := congrArg (fun v ↦ TrivialLieModule.equiv R L R ((ofProd c).symm v).2) h
  simp [centralElement] at h'

/-- Every element of the extension is an element of `L` plus a multiple of `K`. -/
theorem ofProd_eq_add_smul_centralElement (u : L) (z : TrivialLieModule R L R) :
    ofProd c (u, z) = ofProd c (u, 0) + TrivialLieModule.equiv R L R z • centralElement c := by
  apply (ofProd c).symm.injective
  simp only [centralElement, of_symm_add, of_symm_smul, Equiv.symm_apply_apply, Prod.smul_mk,
    smul_zero, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.injEq, true_and]
  apply (TrivialLieModule.equiv R L R).injective
  simp

end LieAlgebra.ofTwoCocycle
