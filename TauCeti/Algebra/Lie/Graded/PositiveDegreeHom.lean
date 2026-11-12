/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Truncation

/-!
# Graded Lie homomorphisms and their truncations

A `TauCeti.GradedLieHom` carries homogeneous pieces along a specified positive degree
map. Its cutoff modulus controls the degree ideals, so the homomorphism descends
from the source truncation at the prescribed order to each target truncation.
These induced maps respect homogeneous pieces, identities, and composition.
They commute with the surjective truncation transitions and remain compatible
when the source cutoff is increased, providing finite-order maps for
inverse-limit constructions.

The cutoff estimate needs only positivity of the source pieces; it does not need
an internal decomposition or injectivity of the degree map. In particular,
distinct source degrees may merge in the target.

The induced maps use `LieIdeal.liftQ`, the universal property of the Lie quotient.
They give the finite-order maps needed to act on compatible families of truncations.
`exists_truncatedMap_iff` characterizes when the underlying map descends at the same
order, independently of the chosen modulus.

Adapted from `Mei/Algebra/Lie/Graded/PositiveDegreeHom.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

namespace TauCeti

section Basic

variable {N M P R L L' L'' : Type*}
  [AddCommMonoid N] [AddCommMonoid M] [AddCommMonoid P] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  {d : PositiveDegrees N} {e : PositiveDegrees M} {p : PositiveDegrees P}

/-- A Lie homomorphism carrying degree `n` to degree `T n`, where `T` includes
the cutoff modulus needed for maps of truncations. -/
structure GradedLieHom (T : PositiveDegreeMap d e)
    (ℒ : N → Submodule R L) (ℳ : M → Submodule R L') extends L →ₗ⁅R⁆ L' where
  /-- Homogeneous elements map to the prescribed homogeneous piece. -/
  map_mem : ∀ {n x}, x ∈ ℒ n → toLieHom x ∈ ℳ (T n)

namespace GradedLieHom

variable {T : PositiveDegreeMap d e} {U : PositiveDegreeMap e p}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'} {ℋ : P → Submodule R L''}

instance : FunLike (GradedLieHom T ℒ ℳ) L L' where
  coe f := f.toLieHom
  coe_injective f g h := by
    have hfg : f.toLieHom = g.toLieHom := DFunLike.coe_injective h
    cases f
    cases g
    cases hfg
    rfl

/-- Changing a propositionally equal degree map does not change the Lie map's values. -/
@[simp]
theorem cast_apply (f : GradedLieHom T ℒ ℳ) {T' : PositiveDegreeMap d e}
    (h : T = T') (x : L) :
    (cast (congrArg (fun V => GradedLieHom V ℒ ℳ) h) f) x = f x := by
  subst T'
  rfl

instance : LinearMapClass (GradedLieHom T ℒ ℳ) R L L' where
  map_add f := f.toLieHom.map_add
  map_smulₛₗ f := f.toLieHom.map_smul

@[simp]
theorem coe_toLieHom (f : GradedLieHom T ℒ ℳ) : ⇑f.toLieHom = f := (rfl)

/-- A graded Lie homomorphism is determined by its values. -/
@[ext]
theorem ext {f g : GradedLieHom T ℒ ℳ} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem map_lie (f : GradedLieHom T ℒ ℳ) (x y : L) :
    f ⁅x, y⁆ = ⁅f x, f y⁆ := f.toLieHom.map_lie x y

/-- The identity graded Lie homomorphism has identity degree map and modulus. -/
def id (ℒ : N → Submodule R L) : GradedLieHom (PositiveDegreeMap.id d) ℒ ℒ where
  toLieHom := LieHom.id
  map_mem hx := by simpa only [LieHom.id_apply, PositiveDegreeMap.id_apply] using hx

@[simp]
theorem id_apply (x : L) : id (d := d) ℒ x = x := (rfl)

/-- The identity Lie homomorphism viewed as a change of positive degree function. -/
def changeDegree (d e : PositiveDegrees N) (hP : d.monoid = e.monoid)
    (ℒ : N → Submodule R L) : GradedLieHom (PositiveDegreeMap.changeDegree d e hP) ℒ ℒ where
  toLieHom := LieHom.id
  map_mem hx := by simpa using hx

@[simp]
theorem changeDegree_apply (d e : PositiveDegrees N) (hP) (ℒ : N → Submodule R L)
    (x : L) : changeDegree d e hP ℒ x = x := (rfl)

@[simp]
theorem changeDegree_toLieHom (d e : PositiveDegrees N) (hP) (ℒ : N → Submodule R L) :
    (changeDegree d e hP ℒ).toLieHom = LieHom.id := (rfl)

/-- Composition carries the composite degree map and its composite cutoff modulus. -/
def comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ) :
    GradedLieHom (U.comp T) ℒ ℋ where
  toLieHom := g.toLieHom.comp f.toLieHom
  map_mem hx := by
    simpa only [PositiveDegreeMap.comp_apply, LieHom.comp_apply] using g.map_mem (f.map_mem hx)

@[simp]
theorem comp_apply (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ) (x : L) :
    g.comp f x = g (f x) := (rfl)

@[simp]
theorem toLieHom_id : (id (d := d) ℒ).toLieHom = LieHom.id := (rfl)

@[simp]
theorem toLieHom_comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ) :
    (g.comp f).toLieHom = g.toLieHom.comp f.toLieHom := (rfl)

/-- The identity on the target is a left identity for composition. -/
@[simp]
theorem id_comp (f : GradedLieHom T ℒ ℳ) :
    cast (congrArg (fun V => GradedLieHom V ℒ ℳ) (PositiveDegreeMap.id_comp T))
      ((id ℳ).comp f) = f := by
  ext x
  simp

/-- The identity on the source is a right identity for composition. -/
@[simp]
theorem comp_id (f : GradedLieHom T ℒ ℳ) :
    cast (congrArg (fun V => GradedLieHom V ℒ ℳ) (PositiveDegreeMap.comp_id T))
      (f.comp (id ℒ)) = f := by
  ext x
  simp

/-- Composition of graded Lie homomorphisms is associative. -/
theorem comp_assoc {Q L3 : Type*} [AddCommMonoid Q] [LieRing L3] [LieAlgebra R L3]
    {q : PositiveDegrees Q} {V : PositiveDegreeMap p q} {ℐ : Q → Submodule R L3}
    (h : GradedLieHom V ℋ ℐ) (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ) :
    cast (congrArg (fun W => GradedLieHom W ℒ ℐ) (PositiveDegreeMap.comp_assoc V U T))
      ((h.comp g).comp f) = h.comp (g.comp f) := by
  ext x
  simpa only [comp_apply] using
    cast_apply ((h.comp g).comp f) (PositiveDegreeMap.comp_assoc V U T) x

end GradedLieHom
end Basic

namespace GradedLieHom

variable {N M P : Type} {R L L' L'' : Type*}
  [AddCommMonoid N] [AddCommMonoid M] [AddCommMonoid P] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  {d : PositiveDegrees N} {e : PositiveDegrees M} {p : PositiveDegrees P}
  {T : PositiveDegreeMap d e} {U : PositiveDegreeMap e p}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'} {ℋ : P → Submodule R L''}
  [DecidableEq N] [DecidableEq M] [DecidableEq P]
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ] [IsPositiveGrading p ℋ]

/-- A graded homomorphism preserves degree ideals at the orders prescribed by its modulus. -/
theorem map_mem_degreeIdeal (f : GradedLieHom T ℒ ℳ) (k : ℕ) {x : L}
    (hx : x ∈ d.degreeIdeal ℒ (T.modulus k)) : f x ∈ e.degreeIdeal ℳ k := by
  apply (LieSubmodule.mem_toSubmodule _).mp
  rw [e.degreeIdeal_toSubmodule]
  have hx' := (LieSubmodule.mem_toSubmodule _).mpr hx
  rw [d.degreeIdeal_toSubmodule] at hx'
  exact (d.map_degreeSubmodule_le ℒ T ℳ f.toLieHom.toLinearMap
    (fun _ _ hx => f.map_mem hx) k) (Submodule.mem_map.mpr ⟨x, hx', rfl⟩)

/-- A graded Lie homomorphism descends uniquely at the same order exactly when
it carries the source degree ideal into the target degree ideal. This criterion
is independent of the chosen cutoff modulus. -/
theorem exists_truncatedMap_iff (f : GradedLieHom T ℒ ℳ) (k : ℕ) :
    (∃! φ : d.truncatedLie ℒ k →ₗ⁅R⁆ e.truncatedLie ℳ k,
      ∀ x : L, φ ((d.degreeIdeal ℒ k).mkQ x) = (e.degreeIdeal ℳ k).mkQ (f x)) ↔
      ∀ x ∈ d.degreeIdeal ℒ k, f x ∈ e.degreeIdeal ℳ k := by
  constructor
  · rintro ⟨φ, hφ, _⟩ x hx
    apply (e.degreeIdeal ℳ k).mkQ_eq_zero.mp
    rw [← hφ, (d.degreeIdeal ℒ k).mkQ_eq_zero.mpr hx, map_zero]
  · intro h
    let φ := (d.degreeIdeal ℒ k).liftQ ((e.degreeIdeal ℳ k).mkQ.comp f.toLieHom) (by
      intro x hx
      rw [LieHom.mem_ker, LieHom.comp_apply, LieIdeal.mkQ_eq_zero]
      exact h x hx)
    have hφ (x : L) : φ ((d.degreeIdeal ℒ k).mkQ x) =
        (e.degreeIdeal ℳ k).mkQ (f x) := (d.degreeIdeal ℒ k).liftQ_apply _ _ x
    refine ⟨φ, hφ, fun ψ hψ => ?_⟩
    exact (d.degreeIdeal ℒ k).lieHom_qext fun x => (hψ x).trans (hφ x).symm

/-- The finite-order Lie homomorphism induced by a graded Lie homomorphism.
The source order may be any `a ≥ T.modulus k`, allowing comparison of cutoffs
without transporting maps between propositionally equal quotient types. -/
def truncatedMap (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ) (h : T.modulus k ≤ a) :
    d.truncatedLie ℒ a →ₗ⁅R⁆ e.truncatedLie ℳ k :=
  (d.degreeIdeal ℒ a).liftQ ((e.degreeIdeal ℳ k).mkQ.comp f.toLieHom) (by
    intro x hx
    rw [LieHom.mem_ker, LieHom.comp_apply, LieIdeal.mkQ_eq_zero]
    exact f.map_mem_degreeIdeal k (d.degreeIdeal_antitone ℒ h hx))

/-- The induced map sends the class of an element to the class of its image. -/
@[simp]
theorem truncatedMap_mk (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) (x : L) :
    f.truncatedMap k h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := by
  exact (d.degreeIdeal ℒ a).liftQ_apply _ _ x

/-- The induced homomorphism commutes with the quotient projections. -/
@[simp]
theorem truncatedMap_mkQ (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) :
    (f.truncatedMap k h).comp (d.degreeIdeal ℒ a).mkQ =
      (e.degreeIdeal ℳ k).mkQ.comp f.toLieHom := by
  ext x
  simp [LieIdeal.mkQ_apply]

/-- The induced map preserves homogeneous pieces along the original degree map. -/
theorem truncatedMap_mem (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) {n : N} {x : d.truncatedLie ℒ a}
    (hx : x ∈ d.truncatedGrading ℒ a n) :
    f.truncatedMap k h x ∈ e.truncatedGrading ℳ k (T n) := by
  obtain ⟨y, hy, rfl⟩ := (d.mem_truncatedGrading_iff ℒ).mp hx
  refine (e.mem_truncatedGrading_iff ℳ).mpr ⟨f y, f.map_mem hy, ?_⟩
  simpa only [LieIdeal.mkQ_apply] using (f.truncatedMap_mk k h y).symm

/-- For an injective degree map, truncation commutes with homogeneous components
at any source cutoff allowed by the modulus. -/
@[simp]
theorem decompose_truncatedMap (f : GradedLieHom T ℒ ℳ) (hT : Function.Injective T)
    {a : ℕ} (k : ℕ) (h : T.modulus k ≤ a) (x : d.truncatedLie ℒ a) (n : N) :
    (DirectSum.decompose (e.truncatedGrading ℳ k) (f.truncatedMap k h x) (T n) :
      e.truncatedLie ℳ k) =
      f.truncatedMap k h
        (DirectSum.decompose (d.truncatedGrading ℒ a) x n : d.truncatedLie ℒ a) :=
  (DirectSum.map_decompose_shift (d.truncatedGrading ℒ a) (e.truncatedGrading ℳ k)
    (f.truncatedMap k h).toLinearMap.toAddMonoidHom T hT
    (fun _ _ hx => f.truncatedMap_mem k h hx) n x).symm

/-- A fixed-degree homomorphism commutes with homogeneous components after truncation,
including when the source cutoff exceeds the target cutoff. -/
@[simp]
theorem decompose_truncatedMap_id {ℳ' : N → Submodule R L'} [GradedLieAlgebra ℳ']
    [IsPositiveGrading d ℳ'] (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ')
    {a : ℕ} (k : ℕ) (h : k ≤ a) (x : d.truncatedLie ℒ a) (n : N) :
    (DirectSum.decompose (d.truncatedGrading ℳ' k)
      (f.truncatedMap k (by simpa using h) x) n : d.truncatedLie ℳ' k) =
      f.truncatedMap k (by simpa using h)
        (DirectSum.decompose (d.truncatedGrading ℒ a) x n : d.truncatedLie ℒ a) := by
  exact (congrArg (fun m => (DirectSum.decompose (d.truncatedGrading ℳ' k)
    (f.truncatedMap k (by simpa using h) x) m : d.truncatedLie ℳ' k))
    (PositiveDegreeMap.id_apply n)).symm.trans
      (f.decompose_truncatedMap (fun i j hij => by simpa using hij) k (by simpa using h) x n)

/-- Truncation sends the identity graded homomorphism to the identity. -/
@[simp]
theorem truncatedMap_id (k : ℕ) :
    (id (d := d) ℒ).truncatedMap k (by simp : (PositiveDegreeMap.id d).modulus k ≤ k) =
      LieHom.id := by
  apply (d.degreeIdeal ℒ k).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply, LieHom.id_apply]

/-- Truncation respects composition, with source orders controlled by successive moduli. -/
theorem truncatedMap_comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ)
    {a b : ℕ} (k : ℕ) (hf : T.modulus b ≤ a) (hg : U.modulus k ≤ b) :
    (g.comp f).truncatedMap k (by
      simpa only [PositiveDegreeMap.comp_modulus] using
        (T.monotone_modulus hg).trans hf) =
      (g.truncatedMap k hg).comp (f.truncatedMap b hf) := by
  apply (d.degreeIdeal ℒ a).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

/-- Increasing the source cutoff changes the induced map only by precomposition
with the source truncation transition. -/
@[simp]
theorem truncatedMap_comp_truncationMap (f : GradedLieHom T ℒ ℳ)
    {k l m : ℕ} (hl : T.modulus k ≤ l) (h : l ≤ m) :
    (f.truncatedMap k hl).comp (d.truncationMap ℒ h) =
      f.truncatedMap k (hl.trans h) := by
  apply (d.degreeIdeal ℒ m).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

/-- Finite graded maps at arbitrary sufficiently large source cutoffs commute
with the quotient transitions. -/
theorem truncationMap_comp_truncatedMap_of_le (f : GradedLieHom T ℒ ℳ)
    {a b k l : ℕ} (hab : a ≤ b) (hkl : k ≤ l)
    (ha : T.modulus k ≤ a) (hb : T.modulus l ≤ b) :
    (e.truncationMap ℳ hkl).comp (f.truncatedMap l hb) =
      (f.truncatedMap k ha).comp (d.truncationMap ℒ hab) := by
  apply (d.degreeIdeal ℒ b).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

/-- The maps of degree truncations commute with the transitions in both towers. -/
theorem truncationMap_comp_truncatedMap (f : GradedLieHom T ℒ ℳ)
    {k l : ℕ} (h : k ≤ l) :
    (e.truncationMap ℳ h).comp (f.truncatedMap l le_rfl) =
      (f.truncatedMap k le_rfl).comp (d.truncationMap ℒ (T.monotone_modulus h)) := by
  exact f.truncationMap_comp_truncatedMap_of_le (T.monotone_modulus h) h le_rfl le_rfl

variable (d ℒ) in
/-- The quotient map onto the order-`k` truncation `L / F^{k+1}L`, as a graded Lie
homomorphism over the identity degree map. -/
def truncation (k : ℕ) :
    GradedLieHom (PositiveDegreeMap.id d) ℒ (d.truncatedGrading ℒ k) where
  toLieHom := (d.degreeIdeal ℒ k).mkQ
  map_mem hx := by
    simpa only [PositiveDegreeMap.id_apply, LieIdeal.mkQ_apply] using
      (d.mem_truncatedGrading_iff ℒ).mpr ⟨_, hx, rfl⟩

@[simp]
theorem toLieHom_truncation (k : ℕ) :
    (truncation d ℒ k).toLieHom = (d.degreeIdeal ℒ k).mkQ := (rfl)

@[simp]
theorem truncation_apply (k : ℕ) (x : L) :
    truncation d ℒ k x = (d.degreeIdeal ℒ k).mkQ x := (rfl)

/-- Truncating the quotient homomorphism at its retained order gives the canonical
map from that quotient to its own degree quotient. -/
@[simp]
theorem truncatedMap_truncation (k : ℕ) :
    (truncation d ℒ k).truncatedMap k (a := k) (by simp) =
      (d.degreeIdeal (d.truncatedGrading ℒ k) k).mkQ := by
  apply (d.degreeIdeal ℒ k).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

end GradedLieHom
end TauCeti
