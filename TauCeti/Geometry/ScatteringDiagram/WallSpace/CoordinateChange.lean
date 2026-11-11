/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Map
public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Basic

/-!
# Coordinate changes of directed wall spaces

An algebraic coordinate change identifies the degree groups and tangent monoids, the
positive monoids, the homogeneous Lie pieces and the wall submodules. Normals
transform by the inverse tangent map. The positive degree functions need not
agree: the finite-maximum cutoff modulus of `PositiveDegreeMap.ofInjectiveOn` gives the
maps at finite order, and its modulus is bounded by the identity modulus when the degree
functions agree.

Coordinate changes form a groupoid: identity, inverse and composition satisfy the
expected laws, and each is determined by its three equivalences. A coordinate change
carries the wall submodule of degree `n` and normal `m` onto that of degree
`T_Γ n` and normal `m ∘ T_Λ⁻¹`. Relabelling the tangent directions of a wall space along
an additive equivalence `T_Λ`, with everything else fixed, is the basic example.

## Attribution

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/CoordinateChange.lean` and
`Mei/Geometry/ScatteringDiagram/WallSpace/TangentChange.lean`
in Mei at commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`. Original copyright and
author credit are retained. The wall-space laws being transported are those of
Leung, Ma and Young, *Refined scattering diagrams and theta functions from asymptotic
analysis of Maurer-Cartan equations*, Definition 1.2.

Source: https://github.com/yuma-mizuno-lean/Mei/tree/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/ScatteringDiagram/WallSpace
-/

public section

namespace TauCeti.DirectedWallSpaces

variable {Γ Γ' Γ'' Λ Λ' Λ'' R L L' L'' : Type*}
  [AddCommMonoid Γ] [AddCommMonoid Γ'] [AddCommMonoid Γ'']
  [AddCommMonoid Λ] [AddCommMonoid Λ'] [AddCommMonoid Λ''] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'} {ℋ : Γ'' → Submodule R L''}

/-- An algebraic coordinate change from directed wall spaces `H` with degrees in `d` to
directed wall spaces `H'` with degrees in `e`. The degree functions may differ, but the
allowed monoids, geometric directions, homogeneous pieces and wall submodules are
identified, with normals transforming contravariantly along the tangent equivalence. -/
structure CoordinateChange (d : PositiveDegrees Γ) (e : PositiveDegrees Γ')
    (H : DirectedWallSpaces ρ ℒ) (H' : DirectedWallSpaces ρ' ℳ) where
  /-- The change of degree coordinates. -/
  degreeEquiv : Γ ≃+ Γ'
  /-- The change of tangent coordinates. -/
  tangentEquiv : Λ ≃+ Λ'
  /-- The isomorphism of coefficient Lie algebras. -/
  lieEquiv : L ≃ₗ⁅R⁆ L'
  /-- Allowed degrees are preserved and reflected. -/
  monoid_mem_iff : ∀ n, degreeEquiv n ∈ e.monoid ↔ n ∈ d.monoid
  /-- The degree and tangent equivalences commute with geometric directions. -/
  map_direction : ∀ n, tangentEquiv (ρ n) = ρ' (degreeEquiv n)
  /-- Homogeneous pieces are identified. -/
  piece_mem_iff : ∀ n x, lieEquiv x ∈ ℳ (degreeEquiv n) ↔ x ∈ ℒ n
  /-- Wall spaces are identified, with contravariant transport of normals. -/
  wall_mem_iff : ∀ n m x,
    lieEquiv x ∈ H'.wall (degreeEquiv n) (m.comp tangentEquiv.symm) ↔ x ∈ H.wall n m

namespace CoordinateChange

variable {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {p : PositiveDegrees Γ''}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  {H'' : DirectedWallSpaces ρ'' ℋ}

/-- A coordinate change is determined by its three equivalences. -/
@[ext]
theorem ext {E F : CoordinateChange d e H H'} (hΓ : E.degreeEquiv = F.degreeEquiv)
    (hΛ : E.tangentEquiv = F.tangentEquiv) (hL : E.lieEquiv = F.lieEquiv) : E = F := by
  cases E
  cases F
  congr

/-- Identity coordinates preserve every directed wall space. -/
def refl (d : PositiveDegrees Γ) (H : DirectedWallSpaces ρ ℒ) : CoordinateChange d d H H where
  degreeEquiv := AddEquiv.refl Γ
  tangentEquiv := AddEquiv.refl Λ
  lieEquiv := LieEquiv.refl
  monoid_mem_iff _ := Iff.rfl
  map_direction _ := rfl
  piece_mem_iff _ _ := Iff.rfl
  wall_mem_iff _ _ _ := by simp

/-- Invert the degree, tangent and Lie coordinate maps. -/
def symm (E : CoordinateChange d e H H') : CoordinateChange e d H' H where
  degreeEquiv := E.degreeEquiv.symm
  tangentEquiv := E.tangentEquiv.symm
  lieEquiv := E.lieEquiv.symm
  monoid_mem_iff n := by simpa using (E.monoid_mem_iff (E.degreeEquiv.symm n)).symm
  map_direction n := by
    apply E.tangentEquiv.injective
    simpa using (E.map_direction (E.degreeEquiv.symm n)).symm
  piece_mem_iff n x := by
    simpa using (E.piece_mem_iff (E.degreeEquiv.symm n) (E.lieEquiv.symm x)).symm
  wall_mem_iff n m x := by
    simpa [AddMonoidHom.comp_assoc] using
      (E.wall_mem_iff (E.degreeEquiv.symm n) (m.comp E.tangentEquiv)
        (E.lieEquiv.symm x)).symm

/-- Compose coordinate changes, applying the left one first. -/
def trans (E : CoordinateChange d e H H') (F : CoordinateChange e p H' H'') :
    CoordinateChange d p H H'' where
  degreeEquiv := E.degreeEquiv.trans F.degreeEquiv
  tangentEquiv := E.tangentEquiv.trans F.tangentEquiv
  lieEquiv := E.lieEquiv.trans F.lieEquiv
  monoid_mem_iff n := (F.monoid_mem_iff _).trans (E.monoid_mem_iff n)
  map_direction n := by simp [E.map_direction, F.map_direction]
  piece_mem_iff n x := (F.piece_mem_iff _ _).trans (E.piece_mem_iff n x)
  wall_mem_iff n m x := by
    have hn : m.comp (E.tangentEquiv.trans F.tangentEquiv).symm =
        (m.comp (E.tangentEquiv.symm : Λ' →+ Λ)).comp (F.tangentEquiv.symm : Λ'' →+ Λ') := by
      ext v
      simp
    rw [hn]
    exact (F.wall_mem_iff _ _ _).trans (E.wall_mem_iff n m x)

@[simp]
theorem refl_degreeEquiv : (refl d H).degreeEquiv = AddEquiv.refl Γ := (rfl)

@[simp]
theorem refl_tangentEquiv : (refl d H).tangentEquiv = AddEquiv.refl Λ := (rfl)

@[simp]
theorem refl_lieEquiv : (refl d H).lieEquiv = LieEquiv.refl := (rfl)

@[simp]
theorem symm_degreeEquiv (E : CoordinateChange d e H H') :
    E.symm.degreeEquiv = E.degreeEquiv.symm := (rfl)

@[simp]
theorem symm_tangentEquiv (E : CoordinateChange d e H H') :
    E.symm.tangentEquiv = E.tangentEquiv.symm := (rfl)

@[simp]
theorem symm_lieEquiv (E : CoordinateChange d e H H') :
    E.symm.lieEquiv = E.lieEquiv.symm := (rfl)

@[simp]
theorem trans_degreeEquiv (E : CoordinateChange d e H H') (F : CoordinateChange e p H' H'') :
    (E.trans F).degreeEquiv = E.degreeEquiv.trans F.degreeEquiv := (rfl)

@[simp]
theorem trans_tangentEquiv (E : CoordinateChange d e H H') (F : CoordinateChange e p H' H'') :
    (E.trans F).tangentEquiv = E.tangentEquiv.trans F.tangentEquiv := (rfl)

@[simp]
theorem trans_lieEquiv (E : CoordinateChange d e H H') (F : CoordinateChange e p H' H'') :
    (E.trans F).lieEquiv = E.lieEquiv.trans F.lieEquiv := (rfl)

/-- Inversion twice recovers the coordinate change. -/
@[simp]
theorem symm_symm (E : CoordinateChange d e H H') : E.symm.symm = E := by
  apply ext <;> rfl

/-- Composing on the right with identity coordinates changes nothing. -/
@[simp]
theorem trans_refl (E : CoordinateChange d e H H') : E.trans (refl e H') = E := by
  apply ext <;> rfl

/-- Composing on the left with identity coordinates changes nothing. -/
@[simp]
theorem refl_trans (E : CoordinateChange d e H H') : (refl d H).trans E = E := by
  apply ext <;> rfl

/-- Composition of coordinate changes is associative. -/
theorem trans_assoc {Γ''' Λ''' L''' : Type*} [AddCommMonoid Γ'''] [AddCommMonoid Λ''']
    [LieRing L'''] [LieAlgebra R L'''] {ρ''' : Γ''' →+ Λ'''} {𝒩 : Γ''' → Submodule R L'''}
    {q : PositiveDegrees Γ'''} {H''' : DirectedWallSpaces ρ''' 𝒩}
    (E : CoordinateChange d e H H') (F : CoordinateChange e p H' H'')
    (G : CoordinateChange p q H'' H''') : (E.trans F).trans G = E.trans (F.trans G) := by
  apply ext <;> rfl

/-- Inverting identity coordinates gives identity coordinates. -/
@[simp]
theorem refl_symm (d : PositiveDegrees Γ) (H : DirectedWallSpaces ρ ℒ) :
    (refl d H).symm = refl d H := by
  apply ext <;> rfl

/-- Inversion reverses composition. -/
@[simp]
theorem symm_trans (E : CoordinateChange d e H H') (F : CoordinateChange e p H' H'') :
    (E.trans F).symm = F.symm.trans E.symm := by
  apply ext <;> rfl

/-- Composing a coordinate change with its inverse gives identity coordinates. -/
@[simp]
theorem self_trans_symm (E : CoordinateChange d e H H') : E.trans E.symm = refl d H := by
  apply ext <;> ext x <;> simp

/-- The inverse coordinate change is also a left inverse. -/
@[simp]
theorem symm_trans_self (E : CoordinateChange d e H H') : E.symm.trans E = refl e H' := by
  apply ext <;> ext x <;> simp

/-- A coordinate change carries the homogeneous piece of degree `n` onto the piece of the
transported degree. -/
theorem map_piece_eq (E : CoordinateChange d e H H') (n : Γ) :
    (ℒ n).map E.lieEquiv.toLieHom.toLinearMap = ℳ (E.degreeEquiv n) := by
  ext y
  obtain ⟨x, rfl⟩ := E.lieEquiv.surjective y
  simpa [Submodule.mem_map] using (E.piece_mem_iff n x).symm

/-- A coordinate change carries the wall submodule of degree `n` and normal `m` onto the
wall submodule of the transported degree and normal `m ∘ T_Λ⁻¹`. -/
theorem map_wall_eq (E : CoordinateChange d e H H') (n : Γ) (m : Λ →+ ℤ) :
    (H.wall n m).map E.lieEquiv.toLieHom.toLinearMap =
      H'.wall (E.degreeEquiv n) (m.comp (E.tangentEquiv.symm : Λ' →+ Λ)) := by
  ext y
  obtain ⟨x, rfl⟩ := E.lieEquiv.surjective y
  simpa [Submodule.mem_map] using (E.wall_mem_iff n m x).symm

/-- The positive degree map of a coordinate change, with the finite-maximum cutoff
modulus: its underlying function is the degree equivalence. -/
noncomputable def degreeMap (E : CoordinateChange d e H H') : PositiveDegreeMap d e :=
  .ofInjectiveOn E.degreeEquiv (fun n hn => (E.monoid_mem_iff n).mpr hn)
    E.degreeEquiv.injective.injOn

@[simp]
theorem degreeMap_apply (E : CoordinateChange d e H H') (n : Γ) :
    E.degreeMap n = E.degreeEquiv n :=
  PositiveDegreeMap.ofInjectiveOn_apply _ _ _ n

/-- The modulus of the degree map is the least source cutoff covering each target cutoff. -/
theorem degreeMap_modulus_le_iff (E : CoordinateChange d e H H') (k l : ℕ) :
    E.degreeMap.modulus k ≤ l ↔
      ∀ n ∈ d.monoid, e.degree (E.degreeEquiv n) ≤ k → d.degree n ≤ l :=
  PositiveDegreeMap.ofInjectiveOn_modulus_le_iff _ _ _ k l

/-- If the source degree is bounded by `c` times the target degree under the degree
equivalence, the modulus at `k` is at most `c * k`. -/
theorem degreeMap_modulus_le_of_degree_le (E : CoordinateChange d e H H') (c k : ℕ)
    (h : ∀ n ∈ d.monoid, d.degree n ≤ c * e.degree (E.degreeEquiv n)) :
    E.degreeMap.modulus k ≤ c * k := by
  rw [E.degreeMap_modulus_le_iff]
  intro n hn hk
  push_cast
  exact (h n hn).trans (mul_le_mul_of_nonneg_left hk (Int.natCast_nonneg c))

/-- If the degree functions agree under the degree equivalence, a coordinate change gives
maps at the same order: the modulus at `k` is at most `k`. -/
theorem degreeMap_modulus_le_of_degree_comp (E : CoordinateChange d e H H')
    (h : e.degree.comp (E.degreeEquiv : Γ →+ Γ') = d.degree) (k : ℕ) :
    E.degreeMap.modulus k ≤ k := by
  simpa using E.degreeMap_modulus_le_of_degree_le 1 k fun n _ => by simp [← h]

end CoordinateChange

namespace CoordinateChange

/-- Relabelling tangent directions along `T` is a coordinate change with identity degree
and Lie coordinates, for any positive degree data. -/
def ofTangentEquiv (d : PositiveDegrees Γ) (H : DirectedWallSpaces ρ ℒ) (T : Λ ≃+ Λ') :
    CoordinateChange d d H (H.mapTangent (T : Λ →+ Λ')) where
  degreeEquiv := AddEquiv.refl Γ
  tangentEquiv := T
  lieEquiv := LieEquiv.refl
  monoid_mem_iff _ := Iff.rfl
  map_direction _ := rfl
  piece_mem_iff _ _ := Iff.rfl
  wall_mem_iff n m x := by
    rw [LieEquiv.refl_apply, AddEquiv.refl_apply, H.mapTangent_wall_comp_symm T n m]

@[simp]
theorem ofTangentEquiv_degreeEquiv (d : PositiveDegrees Γ) (H : DirectedWallSpaces ρ ℒ)
    (T : Λ ≃+ Λ') : (ofTangentEquiv d H T).degreeEquiv = AddEquiv.refl Γ := (rfl)

@[simp]
theorem ofTangentEquiv_tangentEquiv (d : PositiveDegrees Γ) (H : DirectedWallSpaces ρ ℒ)
    (T : Λ ≃+ Λ') : (ofTangentEquiv d H T).tangentEquiv = T := (rfl)

@[simp]
theorem ofTangentEquiv_lieEquiv (d : PositiveDegrees Γ) (H : DirectedWallSpaces ρ ℒ)
    (T : Λ ≃+ Λ') : (ofTangentEquiv d H T).lieEquiv = LieEquiv.refl := (rfl)

end CoordinateChange

end TauCeti.DirectedWallSpaces
