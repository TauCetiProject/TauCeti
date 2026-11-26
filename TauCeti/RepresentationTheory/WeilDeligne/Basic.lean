/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.Constructions

/-!
# Raw Weil–Deligne parameters

Let `E` be a field, `V` an `E`-vector space (finite-dimensional, over a field of characteristic
zero, in the case of interest), `W` a
topological group with an *arithmetic degree* `deg : W →* Multiplicative ℤ` (a homomorphism
`W → ℤ`, read through `(deg w).toAdd`) and `q` a natural number. A
**raw Weil–Deligne parameter** `(V, r, N)` consists of

* a linear representation `r : W → GL(V)` whose kernel is open, and
* a nilpotent endomorphism `N` of `V`, the *monodromy*,

subject to the relation `r(w) N r(w)⁻¹ = q ^ deg w • N` for every `w : W`. The case of interest is
the local Weil group `W = W_K` of a nonarchimedean local field `K`, with its degree and `q` the
cardinality of the residue field; this specialization is `TauCeti.LocalWeilDeligneParameter`.

Frobenius semisimplicity is a separate predicate on the same fields: every `r(w)` with
`deg w ≠ 0` is semisimple. Morphisms of parameters are linear maps intertwining both `r` and `N`,
and isomorphisms are invertible morphisms. A parameter can be transported along a linear
equivalence `e : V ≃ₗ[E] V'`, which conjugates both `r` and `N` by `e`; every isomorphism of
parameters is such a transport (`WeilDeligneParameter.Iso.eq_transport`). Unramified parameters
are in `TauCeti.RepresentationTheory.WeilDeligne.Unramified`.

## Main definitions

* `TauCeti.WeilDeligneParameter E W V deg q`: raw Weil–Deligne parameters on `V`.
* `TauCeti.WeilDeligneParameter.IsFrobeniusSemisimple`: every element of nonzero degree acts
  semisimply.
* `TauCeti.WeilDeligneParameter.Hom`, `TauCeti.WeilDeligneParameter.Iso`: morphisms and
  isomorphisms, extending Mathlib's `Representation.IntertwiningMap` and
  `Representation.Equiv`.
* `TauCeti.WeilDeligneParameter.transport`: transport along a linear equivalence.

## Main results

* `TauCeti.WeilDeligneParameter.transport_refl`,
  `TauCeti.WeilDeligneParameter.transport_transport`: transport is functorial.
* `TauCeti.WeilDeligneParameter.Iso.eq_transport`: an isomorphism `D ≅ D'` exhibits `D'` as the
  transport of `D` along its underlying linear equivalence.
* `TauCeti.WeilDeligneParameter.Iso.isFrobeniusSemisimple_iff`: Frobenius semisimplicity is
  invariant under isomorphism.

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
`deg : W →* Multiplicative ℤ` and a natural number `q`: a linear representation `r` of `W` on `V`
with open kernel, and a nilpotent endomorphism `N` of `V` with `r(w) N r(w)⁻¹ = q ^ deg w • N`.
Frobenius semisimplicity is the separate predicate `WeilDeligneParameter.IsFrobeniusSemisimple`
(Deligne 1973, §8.4.1, p. 568). -/
@[ext]
structure WeilDeligneParameter (E W V : Type*) [Field E] [Group W]
    [TopologicalSpace W] [AddCommGroup V] [Module E V] (deg : W →* Multiplicative ℤ) (q : ℕ) where
  /-- The Weil action. -/
  r : Representation E W V
  /-- The kernel of the Weil action is open. -/
  isOpen_ker : IsOpen (r.ker : Set W)
  /-- The monodromy operator. -/
  N : Module.End E V
  /-- The monodromy is nilpotent. -/
  isNilpotent_N : IsNilpotent N
  /-- An element of degree `n` scales the monodromy by `q ^ n` under conjugation. -/
  conj_N (w : W) : r w * N * r w⁻¹ = (q : E) ^ (deg w).toAdd • N

namespace WeilDeligneParameter

variable {E W V V' V'' V''' : Type*} [Field E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V''] [AddCommGroup V'''] [Module E V''']
  {deg : W →* Multiplicative ℤ} {q : ℕ}

/-- For a continuous degree map, a homomorphism factoring through the degree has open kernel,
because `Multiplicative ℤ` is discrete. -/
theorem isOpen_ker_comp_deg {G : Type*} [MulOneClass G] (hdeg : Continuous deg)
    (f : Multiplicative ℤ →* G) : IsOpen ((f.comp deg).ker : Set W) := by
  rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
  exact hdeg.isOpen_preimage _ (isOpen_discrete _)

/-- The conjugation relation in the form `r(w) N = q ^ deg w • N r(w)`. -/
theorem r_mul_N (D : WeilDeligneParameter E W V deg q) (w : W) :
    D.r w * D.N = (q : E) ^ (deg w).toAdd • (D.N * D.r w) :=
  calc D.r w * D.N = D.r w * D.N * D.r w⁻¹ * D.r w := by simp [mul_assoc, ← map_mul]
    _ = (q : E) ^ (deg w).toAdd • (D.N * D.r w) := by rw [D.conj_N, smul_mul_assoc]

/-- The conjugation relation evaluated at a vector: `r(w) (N v) = q ^ deg w • N (r(w) v)`. -/
theorem r_apply_N_apply (D : WeilDeligneParameter E W V deg q) (w : W) (v : V) :
    D.r w (D.N v) = (q : E) ^ (deg w).toAdd • D.N (D.r w v) :=
  LinearMap.congr_fun (D.r_mul_N w) v

/-- **Frobenius semisimplicity**: every element of the Weil group of nonzero degree acts
semisimply (Deligne 1973, §§8.5–8.6, p. 570). -/
def IsFrobeniusSemisimple (D : WeilDeligneParameter E W V deg q) : Prop :=
  ∀ w, (deg w).toAdd ≠ 0 → Module.End.IsSemisimple (D.r w)

/-- Frobenius semisimplicity means that every element of nonzero degree acts semisimply. -/
theorem isFrobeniusSemisimple_def (D : WeilDeligneParameter E W V deg q) :
    D.IsFrobeniusSemisimple ↔ ∀ w, (deg w).toAdd ≠ 0 → Module.End.IsSemisimple (D.r w) :=
  Iff.rfl

/-- In a Frobenius-semisimple parameter, every element of nonzero degree acts semisimply. -/
theorem IsFrobeniusSemisimple.isSemisimple {D : WeilDeligneParameter E W V deg q}
    (hD : D.IsFrobeniusSemisimple) {w : W} (hw : (deg w).toAdd ≠ 0) :
    Module.End.IsSemisimple (D.r w) :=
  hD w hw

/-! ### Morphisms and isomorphisms -/

/-- **A morphism of raw Weil–Deligne parameters**: a linear map intertwining the Weil actions and
the monodromy operators. -/
structure Hom (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q)
    extends Representation.IntertwiningMap D.r D'.r where
  /-- The map intertwines the monodromy operators. -/
  comp_N : toLinearMap ∘ₗ D.N = D'.N ∘ₗ toLinearMap

namespace Hom

variable {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
  {D'' : WeilDeligneParameter E W V'' deg q} {D''' : WeilDeligneParameter E W V''' deg q}

/-- Morphisms of parameters are determined by their underlying linear maps. -/
@[ext]
theorem ext {f g : Hom D D'} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  congr
  exact Representation.IntertwiningMap.ext h

instance instFunLike : FunLike (Hom D D') V V' where
  coe f := f.toLinearMap
  coe_injective _ _ h := ext (LinearMap.coe_injective h)

instance instLinearMapClass : LinearMapClass (Hom D D') E V V' where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

@[simp]
theorem coe_toIntertwiningMap (f : Hom D D') : ⇑f.toIntertwiningMap = f :=
  rfl

@[simp]
theorem coe_mk (f : Representation.IntertwiningMap D.r D'.r) (h) :
    ⇑(⟨f, h⟩ : Hom D D') = f :=
  rfl

/-- The underlying linear map of a morphism intertwines the Weil actions. -/
theorem comp_r (f : Hom D D') (w : W) : f.toLinearMap ∘ₗ D.r w = D'.r w ∘ₗ f.toLinearMap :=
  f.isIntertwining' w

/-- A morphism intertwines the Weil actions: `f (r(w) v) = r'(w) (f v)`. -/
theorem map_r_apply (f : Hom D D') (w : W) (v : V) : f (D.r w v) = D'.r w (f v) :=
  LinearMap.congr_fun (f.comp_r w) v

/-- A morphism intertwines the monodromy operators: `f (N v) = N' (f v)`. -/
theorem map_N_apply (f : Hom D D') (v : V) : f (D.N v) = D'.N (f v) :=
  LinearMap.congr_fun f.comp_N v

variable (D) in
/-- The identity morphism of a parameter. -/
def id : Hom D D where
  toIntertwiningMap := .id D.r
  comp_N := rfl

/-- The composition of morphisms of parameters. -/
def comp (f : Hom D' D'') (g : Hom D D') : Hom D D'' where
  toIntertwiningMap := f.toIntertwiningMap.comp g.toIntertwiningMap
  comp_N := by
    ext v
    simp [map_N_apply]

theorem id_toIntertwiningMap : (id D).toIntertwiningMap = .id D.r :=
  (rfl)

theorem comp_toIntertwiningMap (f : Hom D' D'') (g : Hom D D') :
    (f.comp g).toIntertwiningMap = f.toIntertwiningMap.comp g.toIntertwiningMap :=
  (rfl)

@[simp]
theorem id_toLinearMap : (id D).toLinearMap = LinearMap.id :=
  (rfl)

@[simp]
theorem comp_toLinearMap (f : Hom D' D'') (g : Hom D D') :
    (f.comp g).toLinearMap = f.toLinearMap ∘ₗ g.toLinearMap :=
  (rfl)

@[simp]
theorem id_apply (v : V) : id D v = v :=
  (rfl)

@[simp]
theorem comp_apply (f : Hom D' D'') (g : Hom D D') (v : V) : f.comp g v = f (g v) :=
  (rfl)

@[simp]
theorem id_comp (f : Hom D D') : (id D').comp f = f := by
  ext1
  simp

@[simp]
theorem comp_id (f : Hom D D') : f.comp (id D) = f := by
  ext1
  simp

theorem comp_assoc (f : Hom D'' D''') (g : Hom D' D'') (h : Hom D D') :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext1
  simp [LinearMap.comp_assoc]

end Hom

/-- **An isomorphism of raw Weil–Deligne parameters**: a linear equivalence intertwining the Weil
actions and the monodromy operators. -/
structure Iso (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q)
    extends toRepresentationEquiv : Representation.Equiv D.r D'.r where
  /-- The equivalence intertwines the monodromy operators. -/
  comp_N : toLinearEquiv.toLinearMap ∘ₗ D.N = D'.N ∘ₗ toLinearEquiv.toLinearMap

namespace Iso

variable {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
  {D'' : WeilDeligneParameter E W V'' deg q} {D''' : WeilDeligneParameter E W V''' deg q}

/-- Isomorphisms of parameters are determined by their underlying linear equivalences. -/
@[ext]
theorem ext {f g : Iso D D'} (h : f.toLinearEquiv = g.toLinearEquiv) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  congr
  exact Representation.Equiv.toLinearEquiv_injective h

instance instEquivLike : EquivLike (Iso D D') V V' where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' _ _ h _ := ext (LinearEquiv.coe_injective h)

instance instLinearEquivClass : LinearEquivClass (Iso D D') E V V' where
  map_add f := f.toLinearEquiv.map_add
  map_smulₛₗ f := f.toLinearEquiv.map_smul

@[simp]
theorem coe_toRepresentationEquiv (f : Iso D D') : ⇑f.toRepresentationEquiv = f :=
  rfl

@[simp]
theorem coe_mk (f : Representation.Equiv D.r D'.r) (h) : ⇑(⟨f, h⟩ : Iso D D') = f :=
  rfl

@[simp]
theorem coe_toLinearEquiv (f : Iso D D') : ⇑f.toLinearEquiv = f :=
  rfl

/-- The underlying linear equivalence of an isomorphism intertwines the Weil actions. -/
theorem comp_r (f : Iso D D') (w : W) :
    f.toLinearEquiv.toLinearMap ∘ₗ D.r w = D'.r w ∘ₗ f.toLinearEquiv.toLinearMap :=
  f.isIntertwining' w

/-- An isomorphism intertwines the Weil actions: `f (r(w) v) = r'(w) (f v)`. -/
theorem map_r_apply (f : Iso D D') (w : W) (v : V) : f (D.r w v) = D'.r w (f v) :=
  LinearMap.congr_fun (f.comp_r w) v

/-- An isomorphism intertwines the monodromy operators: `f (N v) = N' (f v)`. -/
theorem map_N_apply (f : Iso D D') (v : V) : f (D.N v) = D'.N (f v) :=
  LinearMap.congr_fun f.comp_N v

/-- The morphism underlying an isomorphism. -/
def toHom (f : Iso D D') : Hom D D' where
  toIntertwiningMap := f.toIntertwiningMap
  comp_N := f.comp_N

theorem toHom_toIntertwiningMap (f : Iso D D') : f.toHom.toIntertwiningMap = f.toIntertwiningMap :=
  (rfl)

@[simp]
theorem toHom_toLinearMap (f : Iso D D') :
    f.toHom.toLinearMap = f.toLinearEquiv.toLinearMap :=
  (rfl)

@[simp]
theorem coe_toHom (f : Iso D D') : ⇑f.toHom = f :=
  (rfl)

/-- The isomorphism given by a morphism whose underlying map is bijective. -/
def ofBijective (f : Hom D D') (hf : Function.Bijective f) : Iso D D' where
  toRepresentationEquiv := f.toIntertwiningMap.ofBijective hf
  comp_N := by
    ext v
    simpa using f.map_N_apply v

theorem ofBijective_toRepresentationEquiv (f : Hom D D') (hf : Function.Bijective f) :
    (ofBijective f hf).toRepresentationEquiv = f.toIntertwiningMap.ofBijective hf :=
  (rfl)

@[simp]
theorem coe_ofBijective (f : Hom D D') (hf : Function.Bijective f) : ⇑(ofBijective f hf) = f :=
  (rfl)

@[simp]
theorem toHom_ofBijective (f : Hom D D') (hf : Function.Bijective f) :
    (ofBijective f hf).toHom = f := by
  ext1
  ext v
  simp

variable (D) in
/-- The identity isomorphism of a parameter. -/
@[refl] def refl : Iso D D where
  toRepresentationEquiv := .refl D.r
  comp_N := rfl

/-- The inverse of an isomorphism of parameters. -/
@[symm] def symm (f : Iso D D') : Iso D' D where
  toRepresentationEquiv := f.toRepresentationEquiv.symm
  comp_N := by
    ext v
    apply f.injective
    simp only [Representation.Equiv.toLinearMap_symm, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, coe_toLinearEquiv, map_N_apply]
    rw [← coe_toLinearEquiv, LinearEquiv.apply_symm_apply]

/-- The composition of isomorphisms of parameters. -/
@[trans] def trans (f : Iso D D') (g : Iso D' D'') : Iso D D'' where
  toRepresentationEquiv := f.toRepresentationEquiv.trans g.toRepresentationEquiv
  comp_N := by
    ext v
    simp [map_N_apply]

theorem refl_toRepresentationEquiv : (refl D).toRepresentationEquiv = .refl D.r :=
  (rfl)

theorem symm_toRepresentationEquiv (f : Iso D D') :
    f.symm.toRepresentationEquiv = f.toRepresentationEquiv.symm :=
  (rfl)

theorem trans_toRepresentationEquiv (f : Iso D D') (g : Iso D' D'') :
    (f.trans g).toRepresentationEquiv = f.toRepresentationEquiv.trans g.toRepresentationEquiv :=
  (rfl)

@[simp]
theorem refl_toLinearEquiv : (refl D).toLinearEquiv = LinearEquiv.refl E V :=
  (rfl)

@[simp]
theorem symm_toLinearEquiv (f : Iso D D') : f.symm.toLinearEquiv = f.toLinearEquiv.symm :=
  (rfl)

@[simp]
theorem trans_toLinearEquiv (f : Iso D D') (g : Iso D' D'') :
    (f.trans g).toLinearEquiv = f.toLinearEquiv.trans g.toLinearEquiv :=
  (rfl)

@[simp]
theorem refl_apply (v : V) : refl D v = v :=
  (rfl)

@[simp]
theorem trans_apply (f : Iso D D') (g : Iso D' D'') (v : V) : f.trans g v = g (f v) :=
  (rfl)

/-- The inverse of an isomorphism acts by the inverse of its underlying linear equivalence. -/
theorem symm_apply (f : Iso D D') (v : V') : f.symm v = f.toLinearEquiv.symm v :=
  (rfl)

theorem coe_toLinearEquiv_symm (f : Iso D D') : ⇑f.toLinearEquiv.symm = f.symm :=
  (rfl)

/-- The inverse function of an isomorphism is its inverse isomorphism. -/
@[simp]
theorem invFun_eq_symm (f : Iso D D') : f.invFun = f.symm :=
  (rfl)

@[simp]
theorem toHom_refl : (refl D).toHom = Hom.id D := by
  ext1
  ext v
  simp

@[simp]
theorem toHom_trans (f : Iso D D') (g : Iso D' D'') : (f.trans g).toHom = g.toHom.comp f.toHom := by
  ext1
  ext v
  simp

@[simp]
theorem refl_trans (f : Iso D D') : (refl D).trans f = f := by
  ext1
  simp only [trans_toLinearEquiv, refl_toLinearEquiv, LinearEquiv.refl_trans]

@[simp]
theorem trans_refl (f : Iso D D') : f.trans (refl D') = f := by
  ext1
  simp only [trans_toLinearEquiv, refl_toLinearEquiv, LinearEquiv.trans_refl]

theorem trans_assoc (f : Iso D D') (g : Iso D' D'') (h : Iso D'' D''') :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext1
  simp only [trans_toLinearEquiv]
  exact LinearEquiv.trans_assoc _ _ _

@[simp]
theorem apply_symm_apply (f : Iso D D') (v : V') : f (f.symm v) = v :=
  f.toLinearEquiv.apply_symm_apply v

@[simp]
theorem symm_apply_apply (f : Iso D D') (v : V) : f.symm (f v) = v :=
  f.toLinearEquiv.symm_apply_apply v

@[simp]
theorem symm_symm (f : Iso D D') : f.symm.symm = f := by
  ext1
  simp only [symm_toLinearEquiv, LinearEquiv.symm_symm]

@[simp]
theorem refl_symm : (refl D).symm = refl D := by
  ext1
  simp only [symm_toLinearEquiv, refl_toLinearEquiv, LinearEquiv.refl_symm]

@[simp]
theorem trans_symm (f : Iso D D') (g : Iso D' D'') : (f.trans g).symm = g.symm.trans f.symm := by
  ext1
  simp only [symm_toLinearEquiv, trans_toLinearEquiv, LinearEquiv.trans_symm]

@[simp]
theorem self_trans_symm (f : Iso D D') : f.trans f.symm = refl D := by
  ext1
  simp only [trans_toLinearEquiv, symm_toLinearEquiv, refl_toLinearEquiv,
    LinearEquiv.self_trans_symm]

@[simp]
theorem symm_trans_self (f : Iso D D') : f.symm.trans f = refl D' := by
  ext1
  simp only [trans_toLinearEquiv, symm_toLinearEquiv, refl_toLinearEquiv,
    LinearEquiv.symm_trans_self]

end Iso

/-! ### Transport along linear equivalences -/

/-- **Transport of a parameter** along a linear equivalence `e : V ≃ₗ[E] V'`: both the Weil action
and the monodromy are conjugated by `e` (`transport_r_apply`, `transport_N_apply`). -/
def transport (D : WeilDeligneParameter E W V deg q) (e : V ≃ₗ[E] V') :
    WeilDeligneParameter E W V' deg q where
  r := (e.conjAlgEquiv E : Module.End E V →* Module.End E V').comp D.r
  isOpen_ker := by
    convert D.isOpen_ker using 2
    ext w
    simp
  N := e.conjAlgEquiv E D.N
  isNilpotent_N := D.isNilpotent_N.map (e.conjAlgEquiv E)
  conj_N w := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_ofClass, Function.comp_apply, ← map_mul, D.conj_N,
      map_smul]

variable (D : WeilDeligneParameter E W V deg q) (e : V ≃ₗ[E] V') (e' : V' ≃ₗ[E] V'')

theorem transport_r (w : W) : (D.transport e).r w = e.conjAlgEquiv E (D.r w) :=
  (rfl)

@[simp]
theorem transport_r_apply (w : W) (v : V') : (D.transport e).r w v = e (D.r w (e.symm v)) := by
  simp [transport_r, LinearEquiv.conjAlgEquiv_apply]

theorem transport_N : (D.transport e).N = e.conjAlgEquiv E D.N :=
  (rfl)

@[simp]
theorem transport_N_apply (v : V') : (D.transport e).N v = e (D.N (e.symm v)) := by
  simp [transport_N, LinearEquiv.conjAlgEquiv_apply]

/-- Transport along the identity is the identity. -/
@[simp]
theorem transport_refl : D.transport (LinearEquiv.refl E V) = D := by
  ext1
  · ext w v
    simp
  · ext v
    simp

/-- Transporting twice is transporting along the composite. -/
@[simp]
theorem transport_transport : (D.transport e).transport e' = D.transport (e.trans e') := by
  ext1
  · ext w v
    simp
  · ext v
    simp

/-- The isomorphism from a parameter to its transport along `e`, given by `e` itself. -/
def transportIso : Iso D (D.transport e) where
  toRepresentationEquiv := .mk e fun w ↦ by ext v; simp
  comp_N := by ext v; simp

theorem transportIso_toRepresentationEquiv :
    (D.transportIso e).toRepresentationEquiv = .mk e fun w ↦ by ext v; simp :=
  (rfl)

@[simp]
theorem transportIso_toLinearEquiv : (D.transportIso e).toLinearEquiv = e :=
  (rfl)

@[simp]
theorem coe_transportIso : ⇑(D.transportIso e) = e :=
  (rfl)

@[simp]
theorem coe_transportIso_symm : ⇑(D.transportIso e).symm = e.symm := by
  rw [← Iso.coe_toLinearEquiv_symm, transportIso_toLinearEquiv]

variable {D} in
/-- **Isomorphisms are transports**: an isomorphism `f : D ≅ D'` exhibits `D'` as the transport of
`D` along the underlying linear equivalence of `f`. -/
theorem Iso.eq_transport {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') :
    D' = D.transport f.toLinearEquiv := by
  ext1
  · ext w v
    simp [f.map_r_apply]
  · ext v
    simp [f.map_N_apply]

variable {D} in
/-- **Frobenius semisimplicity is invariant under isomorphism.** -/
theorem Iso.isFrobeniusSemisimple_iff {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') :
    D.IsFrobeniusSemisimple ↔ D'.IsFrobeniusSemisimple :=
  forall₂_congr fun w _ ↦ LinearEquiv.isSemisimple_iff _ _ f.toLinearEquiv (f.comp_r w)

/-- Frobenius semisimplicity is invariant under transport. -/
@[simp]
theorem isFrobeniusSemisimple_transport :
    (D.transport e).IsFrobeniusSemisimple ↔ D.IsFrobeniusSemisimple :=
  (D.transportIso e).isFrobeniusSemisimple_iff.symm

end WeilDeligneParameter

end TauCeti
