/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.Instances.Int
public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative

/-!
# Raw Weil–Deligne parameters

Let `E` be a field of characteristic zero, `V` a finite-dimensional `E`-vector space, `W` a
topological group with an *arithmetic degree* `deg : W →* ℤ` and `q` a natural number. A
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

## Main results

* `TauCeti.WeilDeligneParameter.transport_refl`,
  `TauCeti.WeilDeligneParameter.transport_transport`: transport is functorial.
* `TauCeti.WeilDeligneParameter.Iso.eq_transport`: an isomorphism `D ≅ D'` exhibits `D'` as the
  transport of `D` along its underlying linear equivalence.
* `TauCeti.WeilDeligneParameter.Iso.isFrobeniusSemisimple_iff`: Frobenius semisimplicity is
  invariant under isomorphism.
* `TauCeti.WeilDeligneParameter.isFrobeniusSemisimple_unramified_iff`: the unramified parameter of
  `A` is Frobenius semisimple exactly when the degree is trivial or `A` is semisimple.
* `TauCeti.WeilDeligneParameter.not_isFrobeniusSemisimple_unramified_of_isUnipotent_of_ne_one`:
  for a nontrivial degree, an unramified parameter whose Frobenius acts by a nontrivial unipotent
  automorphism, such as the Jordan block `[[1, 1], [0, 1]]`, is not Frobenius semisimple.

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

open LinearMap (GeneralLinearGroup)

/-- **A raw Weil–Deligne parameter** `(V, r, N)` for a topological group `W` with arithmetic degree
`deg : W →* ℤ` and a natural number `q`: a linear representation `r` of `W` on `V` with open
kernel, and a nilpotent endomorphism `N` of `V` with `r(w) N r(w)⁻¹ = q ^ deg w • N`. Frobenius
semisimplicity is the separate predicate `WeilDeligneParameter.IsFrobeniusSemisimple`
(Deligne 1973, §8.4.1, p. 568). -/
@[ext]
structure WeilDeligneParameter (E W V : Type*) [Field E] [CharZero E] [Group W]
    [TopologicalSpace W] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (deg : W →* Multiplicative ℤ) (q : ℕ) where
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

variable {E W V V' V'' V''' : Type*} [Field E] [CharZero E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
  [AddCommGroup V''] [Module E V''] [FiniteDimensional E V'']
  [AddCommGroup V'''] [Module E V'''] [FiniteDimensional E V''']
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

instance : FunLike (Hom D D') V V' where
  coe f := f.toLinearMap
  coe_injective _ _ h := ext (LinearMap.coe_injective h)

instance : LinearMapClass (Hom D D') E V V' where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

@[simp]
theorem coe_toIntertwiningMap (f : Hom D D') : ⇑f.toIntertwiningMap = f :=
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
@[expose] def id : Hom D D where
  toIntertwiningMap := .id D.r
  comp_N := rfl

/-- The composition of morphisms of parameters. -/
@[expose] def comp (f : Hom D' D'') (g : Hom D D') : Hom D D'' where
  toIntertwiningMap := f.toIntertwiningMap.comp g.toIntertwiningMap
  comp_N := by
    rw [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_assoc, g.comp_N,
      ← LinearMap.comp_assoc, f.comp_N, LinearMap.comp_assoc]

@[simp]
theorem id_toLinearMap : (id D).toLinearMap = LinearMap.id :=
  rfl

@[simp]
theorem comp_toLinearMap (f : Hom D' D'') (g : Hom D D') :
    (f.comp g).toLinearMap = f.toLinearMap ∘ₗ g.toLinearMap :=
  rfl

@[simp]
theorem id_apply (v : V) : id D v = v :=
  rfl

@[simp]
theorem comp_apply (f : Hom D' D'') (g : Hom D D') (v : V) : f.comp g v = f (g v) :=
  rfl

@[simp]
theorem id_comp (f : Hom D D') : (id D').comp f = f :=
  rfl

@[simp]
theorem comp_id (f : Hom D D') : f.comp (id D) = f :=
  rfl

theorem comp_assoc (f : Hom D'' D''') (g : Hom D' D'') (h : Hom D D') :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

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

instance : EquivLike (Iso D D') V V' where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' _ _ h _ := ext (LinearEquiv.coe_injective h)

instance : LinearEquivClass (Iso D D') E V V' where
  map_add f := f.toLinearEquiv.map_add
  map_smulₛₗ f := f.toLinearEquiv.map_smul

@[simp]
theorem coe_toRepresentationEquiv (f : Iso D D') : ⇑f.toRepresentationEquiv = f :=
  rfl

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

@[simp]
theorem coe_toHom (f : Iso D D') : ⇑f.toHom = f :=
  rfl

/-- The isomorphism given by a morphism whose underlying map is bijective. -/
@[expose] def ofBijective (f : Hom D D') (hf : Function.Bijective f) : Iso D D' where
  toRepresentationEquiv := .mk (LinearEquiv.ofBijective f.toLinearMap hf) f.comp_r
  comp_N := f.comp_N

@[simp]
theorem coe_ofBijective (f : Hom D D') (hf : Function.Bijective f) : ⇑(ofBijective f hf) = f :=
  rfl

variable (D) in
/-- The identity isomorphism of a parameter. -/
@[expose, refl] def refl : Iso D D where
  toRepresentationEquiv := .refl D.r
  comp_N := rfl

/-- The inverse of an isomorphism of parameters. -/
@[expose, symm] def symm (f : Iso D D') : Iso D' D where
  toRepresentationEquiv := f.toRepresentationEquiv.symm
  comp_N := by
    rw [Representation.Equiv.toLinearMap_symm, LinearEquiv.toLinearMap_symm_comp_eq,
      ← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm]
    exact f.comp_N.symm

/-- The composition of isomorphisms of parameters. -/
@[expose, trans] def trans (f : Iso D D') (g : Iso D' D'') : Iso D D'' where
  toRepresentationEquiv := f.toRepresentationEquiv.trans g.toRepresentationEquiv
  comp_N := (g.toHom.comp f.toHom).comp_N

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

@[simp]
theorem toHom_refl : (refl D).toHom = Hom.id D :=
  rfl

@[simp]
theorem toHom_trans (f : Iso D D') (g : Iso D' D'') : (f.trans g).toHom = g.toHom.comp f.toHom :=
  rfl

@[simp]
theorem refl_trans (f : Iso D D') : (refl D).trans f = f :=
  rfl

@[simp]
theorem trans_refl (f : Iso D D') : f.trans (refl D') = f :=
  rfl

theorem trans_assoc (f : Iso D D') (g : Iso D' D'') (h : Iso D'' D''') :
    (f.trans g).trans h = f.trans (g.trans h) :=
  rfl

@[simp]
theorem symm_symm (f : Iso D D') : f.symm.symm = f :=
  rfl

@[simp]
theorem self_trans_symm (f : Iso D D') : f.trans f.symm = refl D :=
  ext (LinearEquiv.self_trans_symm _)

@[simp]
theorem symm_trans_self (f : Iso D D') : f.symm.trans f = refl D' :=
  ext (LinearEquiv.symm_trans_self _)

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

/-- Transporting twice is transporting along the composite. -/
@[simp]
theorem transport_transport : (D.transport e).transport e' = D.transport (e.trans e') :=
  rfl

/-- The isomorphism from a parameter to its transport along `e`, given by `e` itself. -/
@[expose] def isoTransport : Iso D (D.transport e) where
  toRepresentationEquiv := .mk e fun w ↦ by ext v; simp
  comp_N := by ext v; simp

@[simp]
theorem isoTransport_toLinearEquiv : (D.isoTransport e).toLinearEquiv = e :=
  rfl

variable {D} in
/-- **Isomorphisms are transports**: an isomorphism `f : D ≅ D'` exhibits `D'` as the transport of
`D` along the underlying linear equivalence of `f`. -/
theorem Iso.eq_transport {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') :
    D' = D.transport f.toLinearEquiv :=
  WeilDeligneParameter.ext (MonoidHom.ext fun w ↦ (f.conj_apply_self w).symm)
    ((LinearEquiv.eq_comp_toLinearMap_symm _ _).mpr f.comp_N.symm)

variable {D} in
/-- **Frobenius semisimplicity is invariant under isomorphism.** -/
theorem Iso.isFrobeniusSemisimple_iff {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') :
    D.IsFrobeniusSemisimple ↔ D'.IsFrobeniusSemisimple :=
  forall₂_congr fun w _ ↦ LinearEquiv.isSemisimple_iff _ _ f.toLinearEquiv (f.comp_r w)

/-- Frobenius semisimplicity is invariant under transport. -/
@[simp]
theorem isFrobeniusSemisimple_transport :
    (D.transport e).IsFrobeniusSemisimple ↔ D.IsFrobeniusSemisimple :=
  (D.isoTransport e).isFrobeniusSemisimple_iff.symm

/-! ### Unramified parameters -/

variable (q) in
/-- **The unramified parameter** of a linear automorphism `A` of `V`, for a continuous degree map:
`r(w) = A ^ deg w` and `N = 0`. Elements of degree `0` act trivially. -/
@[expose] def unramified (hdeg : Continuous deg) (A : GeneralLinearGroup E V) :
    WeilDeligneParameter E W V deg q where
  r := (Units.coeHom _).comp ((zpowersHom _ A).comp deg)
  isOpen_ker := by
    rw [← MonoidHom.comp_assoc, MonoidHom.coe_ker, MonoidHom.coe_comp, Set.preimage_comp]
    exact hdeg.isOpen_preimage _ (isOpen_discrete _)
  N := 0
  isNilpotent_N := .zero
  conj_N _ := by simp

@[simp]
theorem unramified_r (hdeg : Continuous deg) (A : GeneralLinearGroup E V) (w : W) :
    (unramified q hdeg A).r w =
      ((A ^ (deg w).toAdd : GeneralLinearGroup E V) : Module.End E V) := by
  simp [unramified]

@[simp]
theorem unramified_N (hdeg : Continuous deg) (A : GeneralLinearGroup E V) :
    (unramified q hdeg A).N = 0 :=
  rfl

/-- **Frobenius semisimplicity of an unramified parameter**: the unramified parameter of `A` is
Frobenius semisimple exactly when the degree is trivial or `A` is semisimple. -/
theorem isFrobeniusSemisimple_unramified_iff (hdeg : Continuous deg)
    (A : GeneralLinearGroup E V) :
    (unramified q hdeg A).IsFrobeniusSemisimple ↔
      deg = 1 ∨ LinearMap.GeneralLinearGroup.IsSemisimple A := by
  simp_rw [isFrobeniusSemisimple_def, unramified_r,
    ← LinearMap.GeneralLinearGroup.isSemisimple_def]
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hd ↦ ?_, ?_⟩
  · obtain ⟨w, hw⟩ : ∃ w, deg w ≠ 1 := by
      by_contra! h'
      exact hd (MonoidHom.ext h')
    have hn : (deg w).toAdd ≠ 0 := by simpa using hw
    exact (LinearMap.GeneralLinearGroup.isSemisimple_zpow_iff hn A).1 (h w hn)
  · rintro (hd | hA) w hw
    · simp [hd] at hw
    · exact hA.zpow _

/-- **A nontrivial unipotent Frobenius is not semisimple**: for a nontrivial degree, if `A ≠ 1` is
unipotent, as for the Jordan block `[[1, 1], [0, 1]]`, then the unramified parameter of `A` is not
Frobenius semisimple. -/
theorem not_isFrobeniusSemisimple_unramified_of_isUnipotent_of_ne_one (hdeg : Continuous deg)
    {A : GeneralLinearGroup E V} (hA : LinearMap.GeneralLinearGroup.IsUnipotent A) (hA₁ : A ≠ 1)
    (hd : deg ≠ 1) : ¬ (unramified q hdeg A).IsFrobeniusSemisimple := by
  rw [isFrobeniusSemisimple_unramified_iff, or_iff_right hd]
  exact fun hss ↦ hA₁ (hss.eq_one_of_isUnipotent hA)

end WeilDeligneParameter

end TauCeti
