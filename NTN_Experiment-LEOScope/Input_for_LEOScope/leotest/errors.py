class Error(Exception):
    pass


class ExporterError(Error):
    def __init__(self, name, message):
        super().__init__()
        self.name = name
        self.message = message

    def __str__(self):
        return self.message


class RunnerError(Error):
    def __init__(self, name, message):
        super().__init__()
        self.name = name
        self.message = message

    def __str__(self):
        return self.message
