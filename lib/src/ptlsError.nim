import strutils
import location

type
  PtlsError* = ref object of Exception
    locs*: seq[Location]

proc returnPtlsError*(header: string, locs: seq[Location] = @[]) : PtlsError =
  return PtlsError(name: header, locs: locs)

proc createPtlsError*(header: string, message: string, locs: seq[Location] = @[]) =
  var e: PtlsError
  new(e)
  e.name = header
  e.msg = message
  e.locs = locs
  raise e

proc toString*(this : PtlsError) : string =
  let sep = "-".repeat(79)
  let locStr = this.locs.join("");
  return sep & "\n" & $this.name & ":\n\n" & this.msg & "\n" & sep & "\n" & locStr
