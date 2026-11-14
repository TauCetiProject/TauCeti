/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Topology

/-!
# Raw Weil–Deligne parameters

Let `E` be a field of characteristic zero, `V` a finite-dimensional `E`-vector space, `W` a
topological group with an *arithmetic degree* `deg : W →* ℤ` and `q` a natural number. A
**raw Weil–Deligne parameter** `(V, r, N)` consists of

* a linear representation `r : W → GL(V)` whose kernel is open, and
* a nilpotent endomorphism `N` of `V`, the *monodromy*,

subject to the relation `r(w) N r(w)⁻¹ = q ^ deg w • N` for every `w : W`. The case of interest is
the local Weil group `W = W_K` of a nonarchimedean local field `K`, with its degree
`TauCeti.ClassFieldTheory.weilDegree K` (normalized so that arithmetic Frobenius lifts have degree
`1`, `TauCeti.ClassFieldTheory.weilDegree_eq_ofAdd_one_iff`) and `q` the cardinality of the residue
field; this is `TauCeti.LocalWeilDeligneParameter K E V`.

Frobenius semisimplicity is a separate predicate on the same fields: every `r(w)` with
`deg w ≠ 0` is semisimple. Morphisms of parameters are linear maps intertwining both `r` and `N`,
and isomorphisms are invertible morphisms. A parameter can be transported along a linear
equivalence `e : V ≃ₗ[E] V'`, which conjugates both `r` and `N` by `e`; every isomorphism of
parameters is such a transport (`WeilDeligneParameter.Iso.eq_transport`).

## Main definitions

* `TauCeti.WeilDeligneParameter E W V deg q`: raw Weil–Deligne parameters on `V`.
* `TauCeti.WeilDeligneParameter.IsFrobeniusSemisimple`: every element of nonzero degree acts
  semisimply.
* `TauCeti.WeilDeligneParameter.Hom`, `TauCeti.WeilDeligneParameter.Iso`: morphisms and
  isomorphisms, extending Mathlib's `Representation.IntertwiningMap` and
  `Representation.Equiv`.
* `TauCeti.WeilDeligneParameter.transport`: transport along a linear equivalence.
* `TauCeti.WeilDeligneParameter.unramified`: the parameter with `r(w) = A ^ deg w` and `N = 0`.
* `TauCeti.LocalWeilDeligneParameter K E V`: the parameters of the local Weil group of `K`.

## Main results

* `TauCeti.WeilDeligneParameter.transport_refl`, `TauCeti.WeilDeligneParameter.transport_trans`:
  transport is functorial.
* `TauCeti.WeilDeligneParameter.Iso.eq_transport`: an isomorphism `D ≅ D'` exhibits `D'` as the
  transport of `D` along its underlying linear equivalence.
* `TauCeti.WeilDeligneParameter.Iso.isFrobeniusSemisimple_iff`: Frobenius semisimplicity is
  invariant under isomorphism.
* `TauCeti.WeilDeligneParameter.not_isFrobeniusSemisimple_unramified`: an unramified parameter
  whose Frobenius acts by a nontrivial unipotent automorphism, such as the Jordan block
  `[[1, 1], [0, 1]]`, is not Frobenius semisimple.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568, and §§8.5–8.6, p. 570.
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §4.1.
-/

public section

noncomputable section

namespace TauCeti

open Module

/-- **A raw Weil–Deligne parameter** `(V, r, N)` for a topological group `W` with arithmetic degree
`deg : W →* ℤ` and a natural number `q`: a linear representation `r` of `W` on `V` with open
kernel, and a nilpotent endomorphism `N` of `V` with `r(w) N r(w)⁻¹ = q ^ deg w • N`. Frobenius
semisimplicity is the separate predicate `WeilDeligneParameter.IsFrobeniusSemisimple`
([Del73], §8.4.1, p. 568). -/
@[ext]
structure WeilDeligneParameter (E W V : Type*) [Field E] [CharZero E] [Group W]
    [TopologicalSpace W] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (deg : W →* Multiplicative ℤ) (q : ℕ) where
  /-- The Weil action. -/
  r : Representation E W V
  /-- The Weil action is locally constant: its kernel is open. -/
  isOpen_ker : IsOpen (r.ker : Set W)
  /-- The monodromy operator. -/
  N : Module.End E V
  /-- The monodromy is nilpotent. -/
  isNilpotent_N : IsNilpotent N
  /-- An element of degree `n` scales the monodromy by `q ^ n` under conjugation. -/
  conj_N (w : W) : r w * N * r w⁻¹ = (q : E) ^ (deg w).toAdd • N

namespace WeilDeligneParameter

variable {E W V V' V'' : Type*} [Field E] [CharZero E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
  [AddCommGroup V''] [Module E V''] [FiniteDimensional E V'']
  {deg : W →* Multiplicative ℤ} {q : ℕ}

/-- The conjugation relation in the form `r(w) N = q ^ deg w • N r(w)`. -/
theorem r_mul_N (D : WeilDeligneParameter E W V deg q) (w : W) :
    D.r w * D.N = (q : E) ^ (deg w).toAdd • (D.N * D.r w) := by
  rw [← smul_mul_assoc, ← D.conj_N, mul_assoc _ (D.r w⁻¹), ← map_mul, inv_mul_cancel, map_one,
    mul_one]

/-- The conjugation relation evaluated at a vector: `r(w) (N v) = q ^ deg w • N (r(w) v)`. -/
theorem r_apply_N_apply (D : WeilDeligneParameter E W V deg q) (w : W) (v : V) :
    D.r w (D.N v) = (q : E) ^ (deg w).toAdd • D.N (D.r w v) :=
  LinearMap.congr_fun (D.r_mul_N w) v

/-- **Frobenius semisimplicity**: every element of the Weil group of nonzero degree acts
semisimply ([Del73], §§8.5–8.6, p. 570). -/
def IsFrobeniusSemisimple (D : WeilDeligneParameter E W V deg q) : Prop :=
  ∀ w, (deg w).toAdd ≠ 0 → Module.End.IsSemisimple (D.r w)

/-! ### Morphisms and isomorphisms -/

/-- **A morphism of raw Weil–Deligne parameters**: a linear map intertwining the Weil actions and
the monodromy operators. -/
structure Hom (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q)
    extends Representation.IntertwiningMap D.r D'.r where
  /-- The map intertwines the monodromy operators. -/
  comp_N : toLinearMap ∘ₗ D.N = D'.N ∘ₗ toLinearMap

namespace Hom

variable {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
  {D'' : WeilDeligneParameter E W V'' deg q}

/-- Morphisms of parameters are determined by their underlying linear maps. -/
@[ext]
theorem ext {f g : Hom D D'} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  congr
  exact Representation.IntertwiningMap.ext h

variable (D) in
/-- The identity morphism of a parameter. -/
@[expose] def id : Hom D D where
  toIntertwiningMap := .id D.r
  comp_N := rfl

/-- The composition of morphisms of parameters. -/
@[expose] def comp (f : Hom D' D'') (g : Hom D D') : Hom D D'' where
  toIntertwiningMap := f.toIntertwiningMap.comp g.toIntertwiningMap
  comp_N := by
    change (f.toLinearMap ∘ₗ g.toLinearMap) ∘ₗ D.N = D''.N ∘ₗ f.toLinearMap ∘ₗ g.toLinearMap
    rw [LinearMap.comp_assoc, g.comp_N, ← LinearMap.comp_assoc, f.comp_N, LinearMap.comp_assoc]

@[simp]
theorem id_toLinearMap : (id D).toLinearMap = LinearMap.id :=
  rfl

@[simp]
theorem comp_toLinearMap (f : Hom D' D'') (g : Hom D D') :
    (f.comp g).toLinearMap = f.toLinearMap ∘ₗ g.toLinearMap :=
  rfl

@[simp]
theorem id_comp (f : Hom D D') : (id D').comp f = f :=
  rfl

@[simp]
theorem comp_id (f : Hom D D') : f.comp (id D) = f :=
  rfl

end Hom

/-- **An isomorphism of raw Weil–Deligne parameters**: a linear equivalence intertwining the Weil
actions and the monodromy operators. -/
structure Iso (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q)
    extends toRepEquiv : Representation.Equiv D.r D'.r where
  /-- The equivalence intertwines the monodromy operators. -/
  comp_N : toLinearEquiv.toLinearMap ∘ₗ D.N = D'.N ∘ₗ toLinearEquiv.toLinearMap

namespace Iso

variable {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
  {D'' : WeilDeligneParameter E W V'' deg q}

/-- Isomorphisms of parameters are determined by their underlying linear equivalences. -/
@[ext]
theorem ext {f g : Iso D D'} (h : f.toLinearEquiv = g.toLinearEquiv) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  congr
  exact Representation.Equiv.toLinearEquiv_injective h

/-- The underlying linear equivalence of an isomorphism intertwines the Weil actions. -/
theorem comp_r (f : Iso D D') (w : W) :
    f.toLinearEquiv.toLinearMap ∘ₗ D.r w = D'.r w ∘ₗ f.toLinearEquiv.toLinearMap :=
  f.isIntertwining' w

/-- The morphism underlying an isomorphism. -/
@[expose] def toHom (f : Iso D D') : Hom D D' where
  toIntertwiningMap := f.toIntertwiningMap
  comp_N := f.comp_N

@[simp]
theorem toHom_toLinearMap (f : Iso D D') :
    f.toHom.toLinearMap = f.toLinearEquiv.toLinearMap :=
  rfl

variable (D) in
/-- The identity isomorphism of a parameter. -/
@[expose] def refl : Iso D D where
  toRepEquiv := .refl D.r
  comp_N := rfl

/-- The inverse of an isomorphism of parameters. -/
@[expose] def symm (f : Iso D D') : Iso D' D where
  toRepEquiv := f.toRepEquiv.symm
  comp_N := by
    ext v
    apply f.toLinearEquiv.injective
    have h := LinearMap.congr_fun f.comp_N (f.toLinearEquiv.symm v)
    change f.toLinearEquiv (f.toLinearEquiv.symm (D'.N v)) =
      f.toLinearEquiv (D.N (f.toLinearEquiv.symm v))
    rw [LinearEquiv.apply_symm_apply]
    exact (h.trans (congrArg D'.N (f.toLinearEquiv.apply_symm_apply v))).symm

/-- The composition of isomorphisms of parameters. -/
@[expose] def trans (f : Iso D D') (g : Iso D' D'') : Iso D D'' where
  toRepEquiv := f.toRepEquiv.trans g.toRepEquiv
  comp_N := by
    change (g.toLinearEquiv.toLinearMap ∘ₗ f.toLinearEquiv.toLinearMap) ∘ₗ D.N =
      D''.N ∘ₗ g.toLinearEquiv.toLinearMap ∘ₗ f.toLinearEquiv.toLinearMap
    rw [LinearMap.comp_assoc, f.comp_N, ← LinearMap.comp_assoc, g.comp_N, LinearMap.comp_assoc]

@[simp]
theorem refl_toLinearEquiv : (refl D).toLinearEquiv = LinearEquiv.refl E V :=
  rfl

@[simp]
theorem symm_toLinearEquiv (f : Iso D D') : f.symm.toLinearEquiv = f.toLinearEquiv.symm :=
  rfl

@[simp]
theorem trans_toLinearEquiv (f : Iso D D') (g : Iso D' D'') :
    (f.trans g).toLinearEquiv = f.toLinearEquiv.trans g.toLinearEquiv :=
  rfl

end Iso

/-! ### Transport along linear equivalences -/

/-- **Transport of a parameter** along a linear equivalence `e : V ≃ₗ[E] V'`: both the Weil action
and the monodromy are conjugated by `e` (`transport_r_apply`, `transport_N_apply`). -/
@[expose] def transport (D : WeilDeligneParameter E W V deg q) (e : V ≃ₗ[E] V') :
    WeilDeligneParameter E W V' deg q where
  r := (e.conjAlgEquiv E : Module.End E V →* Module.End E V').comp D.r
  isOpen_ker := by
    convert D.isOpen_ker using 2
    ext w
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
      Function.comp_apply]
    exact map_eq_one_iff _ (e.conjAlgEquiv E).injective
  N := e.conjAlgEquiv E D.N
  isNilpotent_N := D.isNilpotent_N.map (e.conjAlgEquiv E)
  conj_N w := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_ofClass, Function.comp_apply, ← map_mul, D.conj_N,
      map_smul]

variable (D : WeilDeligneParameter E W V deg q) (e : V ≃ₗ[E] V') (e' : V' ≃ₗ[E] V'')

theorem transport_r (w : W) : (D.transport e).r w = e.conjAlgEquiv E (D.r w) :=
  rfl

@[simp]
theorem transport_r_apply (w : W) (v : V') : (D.transport e).r w v = e (D.r w (e.symm v)) :=
  rfl

theorem transport_N : (D.transport e).N = e.conjAlgEquiv E D.N :=
  rfl

@[simp]
theorem transport_N_apply (v : V') : (D.transport e).N v = e (D.N (e.symm v)) :=
  rfl

/-- Transport along the identity is the identity. -/
@[simp]
theorem transport_refl : D.transport (LinearEquiv.refl E V) = D :=
  rfl

/-- Transport along a composite is the composite of the transports. -/
theorem transport_trans : D.transport (e.trans e') = (D.transport e).transport e' :=
  rfl

/-- The isomorphism from a parameter to its transport along `e`, given by `e` itself. -/
@[expose] def isoTransport : Iso D (D.transport e) where
  toRepEquiv := .mk e fun w ↦ by ext v; simp
  comp_N := by ext v; simp

@[simp]
theorem isoTransport_toLinearEquiv : (D.isoTransport e).toLinearEquiv = e :=
  rfl

/-- **Isomorphisms are transports**: an isomorphism `f : D ≅ D'` exhibits `D'` as the transport of
`D` along the underlying linear equivalence of `f`. -/
theorem Iso.eq_transport {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') :
    D' = D.transport f.toLinearEquiv := by
  ext1
  · ext w v
    exact ((LinearMap.congr_fun (f.comp_r w) (f.toLinearEquiv.symm v)).trans
      (congrArg (D'.r w) (f.toLinearEquiv.apply_symm_apply v))).symm
  · ext v
    exact ((LinearMap.congr_fun f.comp_N (f.toLinearEquiv.symm v)).trans
      (congrArg D'.N (f.toLinearEquiv.apply_symm_apply v))).symm

/-- **Frobenius semisimplicity is invariant under isomorphism.** -/
theorem Iso.isFrobeniusSemisimple_iff {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') :
    D.IsFrobeniusSemisimple ↔ D'.IsFrobeniusSemisimple :=
  forall₂_congr fun w _ ↦ LinearEquiv.isSemisimple_iff _ _ f.toLinearEquiv (f.comp_r w)

/-- Frobenius semisimplicity is preserved by transport. -/
theorem IsFrobeniusSemisimple.transport {D : WeilDeligneParameter E W V deg q}
    (hD : D.IsFrobeniusSemisimple) : (D.transport e).IsFrobeniusSemisimple :=
  (D.isoTransport e).isFrobeniusSemisimple_iff.1 hD

/-! ### Unramified parameters -/

/-- **The unramified parameter** of an automorphism `A` of `V`, for a continuous degree map:
`r(w) = A ^ deg w` and `N = 0`. Its kernel contains the kernel of the degree, which is open
because `deg` is continuous for the discrete topology on `ℤ`. -/
@[expose] def unramified (hdeg : Continuous deg) (A : (Module.End E V)ˣ) :
    WeilDeligneParameter E W V deg q where
  r := (Units.coeHom _).comp ((zpowersHom _ A).comp deg)
  isOpen_ker := by
    change IsOpen (deg ⁻¹' {n | ((zpowersHom _ A n : (Module.End E V)ˣ) : Module.End E V) = 1})
    exact hdeg.isOpen_preimage _ (isOpen_discrete _)
  N := 0
  isNilpotent_N := .zero
  conj_N _ := by simp

@[simp]
theorem unramified_r (hdeg : Continuous deg) (A : (Module.End E V)ˣ) (w : W) :
    (unramified (q := q) hdeg A).r w = ((A ^ (deg w).toAdd : (Module.End E V)ˣ) : Module.End E V) :=
  rfl

@[simp]
theorem unramified_N (hdeg : Continuous deg) (A : (Module.End E V)ˣ) :
    (unramified (q := q) hdeg A).N = 0 :=
  rfl

/-- **A nontrivial unipotent Frobenius is not semisimple**: if some element of `W` has degree `1`
and `A ≠ 1` is unipotent, as for the Jordan block `[[1, 1], [0, 1]]`, then the unramified
parameter of `A` is not Frobenius semisimple. -/
theorem not_isFrobeniusSemisimple_unramified (hdeg : Continuous deg) {A : (Module.End E V)ˣ}
    (hA : IsNilpotent ((A : Module.End E V) - 1)) (hA₁ : A ≠ 1)
    (hw : ∃ w, deg w = Multiplicative.ofAdd 1) :
    ¬ (unramified (q := q) hdeg A).IsFrobeniusSemisimple := fun hD ↦ by
  obtain ⟨w, hw⟩ := hw
  have hss := hD w (by simp [hw])
  rw [unramified_r, hw, toAdd_ofAdd, zpow_one] at hss
  have h₀ : (A : Module.End E V) - algebraMap E (Module.End E V) 1 = 0 :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple (by rwa [map_one])
      (Module.End.isSemisimple_sub_algebraMap_iff.2 hss)
  exact hA₁ (Units.ext (by rwa [map_one, sub_eq_zero] at h₀))

end WeilDeligneParameter

/-! ### Parameters of the local Weil group -/

open _root_.ValuativeRel in
/-- **Raw Weil–Deligne parameters of a nonarchimedean local field** `K`: the parameters of the
local Weil group `W_K` with its Weil topology and arithmetic degree, and `q` the cardinality of the
residue field of `K`. -/
abbrev LocalWeilDeligneParameter (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (E V : Type*) [Field E] [CharZero E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] :=
  WeilDeligneParameter E (ClassFieldTheory.WeilGroup K) V (ClassFieldTheory.weilDegree K)
    (Nat.card 𝓀[K])

end TauCeti
